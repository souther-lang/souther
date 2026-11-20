package souther.compiler.codegen;

import souther.compiler.check.Boundary;
import souther.compiler.codegen.BodyGen.Places;
import souther.compiler.check.Elaborator;
import souther.compiler.check.Lower;
import souther.compiler.check.DerivedSymbols;
import souther.compiler.ast.Hir;
import souther.compiler.core.BoundaryConstraint;
import souther.compiler.core.ConstraintProjection;
import souther.compiler.core.MessageForm;
import souther.compiler.core.ValueShape;
import souther.compiler.diag.Diagnostic;
import net.unit8.notation199x.pattern.PatternMeaning;
import souther.compiler.types.BindingId;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.CaseShape;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.check.TypeOps;
import souther.compiler.core.Core;

import souther.compiler.jvm.GeneratedClass;
import java.lang.classfile.ClassBuilder;
import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.classfile.MethodSignature;
import java.lang.classfile.attribute.SignatureAttribute;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.DynamicCallSiteDesc;
import java.lang.constant.DynamicConstantDesc;
import java.lang.constant.MethodHandleDesc;
import java.lang.constant.MethodTypeDesc;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.HashMap;
import java.util.Map;
import java.util.SequencedMap;

import static souther.compiler.codegen.Descriptors.*;
import static souther.compiler.codegen.JvmTypes.*;

/**
 * Generates a data/sum/unit type's decoder and encoder (spec §codec-generation, §case-propagation):
 * object/leaf/newtype/sum decoding, a newtype's invariant as constraints, the construct check, and
 * the encoder raw expressions.
 *
 * <p>What it emits stands on {@code souther.runtime.boundary} and on nothing else: a decoder is
 * composed of {@code Decoding}'s parts and reads its input through the {@code TreeReader} it is
 * handed, so one decoder per type reads every source a binding brings, and no decoder library is
 * named by a generated class (spec §jvm-codec). Name resolution and the synthetic-class sink come
 * from {@link CodegenContext}; body expressions are emitted through a {@link BodyGen} built per
 * method.
 */
final class CodecGen {

    private final CodegenContext ctx;
    private final DerivedSymbols symbols;

    /** The $Dec class currently being generated — the owner of the helpers its decode body calls.
     *  Set per {@link #generateDecoderClass}. */
    private ClassDesc decoderClass;

    /** The value class the decoder being generated builds. Its {@code $Ctfe} carries the clause
     *  predicates a refined constraint reaches for, and asking for that class by the type it belongs
     *  to is what keeps the two from being named apart. Set beside {@link #decoderClass}. */
    private GeneratedClass.Value decodedValue;

    /** The name of the data the decoder being generated builds, which a clause's refusal names as
     *  the rejecting type. Set beside {@link #decoderClass}. */
    private String decodedName;

    /** The patterns the decoder being generated holds a value to, and the constants their machines
     *  are loaded from ({@link #patternConstantsOf}). Set beside {@link #decoderClass}. */
    private Map<PatternMeaning, DynamicConstantDesc<Object>> patternConstants = Map.of();

    CodecGen(CodegenContext ctx) {
        this.ctx = ctx;
        this.symbols = ctx.symbols;
    }

    private ClassDesc cd(GeneratedClass generated) { return ctx.cd(generated); }
    private GeneratedClass.Value valueOf(Hir.Def def) { return new GeneratedClass.Value(def.declares()); }
    private GeneratedClass decoderOf(Hir.Def def) { return new GeneratedClass.Decoder(valueOf(def)); }
    private ClassDesc cd(Hir.Def def) { return ctx.cd(def); }
    private ClassDesc cd(TypeSymbol typeName) { return ctx.cd(typeName); }
    private void unbox(CodeBuilder code, Type type, int slot) { JvmTypes.unbox(code, type, slot, ctx); }

    /** The {@code invokedynamic} call site that produces a {@code Function} wrapping
     *  {@code Sets::fromList} (a {@code List -> Set} dedup), for {@code Decoder.map} in a Set decoder. */
    private DynamicCallSiteDesc setFromListCallSite() {
        DirectMethodHandleDesc impl = ctx.boundRuntime(CD_Sets, "fromList",
                MethodTypeDesc.of(CD_Set, CD_List), Work.CHECKPOINTED);
        return Lambdas.callSite(Lambdas.Sam.FUNCTION, impl, MethodTypeDesc.of(CD_Set, CD_List));
    }

    /**
     * Pushes the leaf decoder of a scalar: {@code Decoding}'s own, which reads it through the reader
     * a decode is handed.
     *
     * <p>Text is let in there — refused where it holds half of a surrogate pair, canonicalized to NFC
     * otherwise — before anything reads it, so every string that reaches the domain from outside is
     * canonical whatever shape it arrived in: a field, a newtype's base, a map's key, a list or set
     * element, a sum's discriminator, an enumeration's name, a temporal before it is parsed.
     * {@code ADecoderCanonicalizesEveryShapeTest} walks the decoder shapes to hold that.
     */
    private static void emitLeafDecoder(CodeBuilder code, LeafScalar kind) {
        code.invokestatic(CD_Decoding, leafName(kind), MTD_decoder);
    }

    /**
     * Pushes the decoder a map key is read with. A key always arrives as a {@code String}, so a
     * temporal key is its leaf reading text.
     */
    private void emitKeyDecoder(CodeBuilder code, MapKeyRepresentation key) {
        switch (key) {
            // a named key runs its own decoder: a newtype's applies its invariant, an enumeration's
            // reads the case name
            case MapKeyRepresentation.NamedKey n -> invokeCodec(code, n.name(), "decoder", MTD_decoder);
            case MapKeyRepresentation.Lexical l -> emitLeafDecoder(code, l.leaf());
        }
    }

    /**
     * Pushes a {@code Function<K, String>} rendering a key as the text it crosses as, for
     * {@code Maps.mapKeys} before the String-keyed map encoder runs.
     *
     * <p>It is the key type's own encoder in both arms — a leaf encoder for a primitive, the derived
     * {@code encoder()} for a named key — so what a name wraps is never read here. That is what
     * keeps this call site out of the admissible set: a newtype over a base admitted later writes
     * itself through the same two instructions, with nothing to add.
     *
     * <p>The same two {@code Runner.encodeKey} takes, reflectively. Both go through an encoder rather
     * than through an accessor, so neither can spell a key the other would not.
     */
    private void pushKeyRenderer(CodeBuilder code, MapKeyRepresentation key) {
        switch (key) {
            case MapKeyRepresentation.NamedKey n -> invokeCodec(code, n.name(), "encoder", MTD_encoder);
            case MapKeyRepresentation.Lexical l ->
                    code.invokestatic(CD_Encoding, leafName(l.leaf()), MTD_encoder);
        }
        code.invokedynamic(encodeAsFunctionCallSite());     // Encoder<K, Object> -> Function<K, String>
    }

    /** Whether a map's keys are rendered before the String-keyed encoder sees them: a {@code String}
     *  key is already what it wants. */
    private static boolean needsKeyRender(MapKeyRepresentation key) {
        return !(key instanceof MapKeyRepresentation.Text);
    }

    /** Invokes a type's static {@code decoder()}/{@code encoder()} factory, as an interface
     * method reference when the type is a sum (its factory lives on a sealed interface). */
    private void invokeCodec(CodeBuilder code, Hir.Name typeName, String method, MethodTypeDesc mtd) {
        invokeCodec(code, Backend.names(typeName), method, mtd);
    }

    private void invokeCodec(CodeBuilder code, TypeSymbol type, String method, MethodTypeDesc mtd) {
        code.invokestatic(cd(type), method, mtd, symbols.declaredNode(type) instanceof Hir.SumData);
    }

    byte[] generateSumEncoder(Hir.SumData sum, Boundary.Alternatives alternatives) {
        Boundary.Representation.Discriminated form = discriminated(alternatives);
        ClassDesc cdEnc = cd(new GeneratedClass.Encoder(valueOf(sum)));
        return build(cdEnc, cb -> {
            beginCodecClass(cb, CD_Encoder, cdEnc);
            // Dispatch on the runtime case type, encode that case as it writes itself, then add what
            // membership in this sum requires of it (spec §encoder-derivation).
            cb.withMethodBody("encode", MTD_encode, ClassFile.ACC_PUBLIC, code -> {
                for (Boundary.WireCase v : alternatives.wireCases()) {
                    TypeSymbol caseName = v.atom();
                    code.aload(1);
                    code.instanceOf(cd(caseName));
                    Label next = code.newLabel();
                    code.ifeq(next);
                    emitTagged(code, TypeOps.caseShape(caseName, symbols), form, v.tag(), () -> {
                        invokeCodec(code, caseName, "encoder", MTD_encoder);
                        code.aload(1);
                        code.invokeinterface(CD_Encoder, "encode", MTD_encode);
                    });
                    code.areturn();
                    code.labelBinding(next);
                }
                code.new_(CD_IllegalStateException);
                code.dup();
                code.invokespecial(CD_IllegalStateException, "<init>", MTD_void);
                code.athrow();
            });
        });
    }

    /** The flags, the interface, the constructor and the shared instance every codec class has. */
    private static void beginCodecClass(ClassBuilder cb, ClassDesc iface, ClassDesc self) {
        cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
        cb.withInterfaceSymbols(iface);
        emitDefaultCtor(cb);
        emitSharedInstance(cb, self);
    }

    /** {@code decoder.decode(in, path, reader)}, for the decoder on the stack, with the arguments the
     *  decode being written was handed: this=0, in=1, path=2, reader=3. */
    private static void decodeWhatThisWasHanded(CodeBuilder code) {
        code.aload(1);
        code.aload(2);
        code.aload(3);
        code.invokeinterface(CD_Decoder, "decode", MTD_decode);
    }

    /**
     * Decodes a sum whose cases are told apart by a discriminator (spec §sum-discrimination): the tag
     * is read from the discriminator key, and each case is read by that case's decoder.
     *
     * <p>The mirror of what the encoder wrote: a case that wears the envelope is handed what is under
     * the contents key and reads it as the standalone value it is, while a product and a unit read
     * the discriminated object they are part of.
     */
    byte[] generateSumDecoder(Hir.SumData sum, Boundary.Alternatives alternatives) {
        Boundary.Representation.Discriminated form = discriminated(alternatives);
        List<Boundary.WireCase> wireCases = alternatives.wireCases();
        ClassDesc cdDec = cd(decoderOf(sum));
        return build(cdDec, cb -> {
            beginCodecClass(cb, CD_Decoder, cdDec);
            cb.withMethodBody("decode", MTD_decode, ClassFile.ACC_PUBLIC, code -> {
                code.loadConstant(form.tagKey());
                pushInt(code, wireCases.size());
                code.anewarray(CD_String);
                for (int i = 0; i < wireCases.size(); i++) {
                    code.dup();
                    pushInt(code, i);
                    code.loadConstant(wireCases.get(i).tag());
                    code.aastore();
                }
                pushInt(code, wireCases.size());
                code.anewarray(CD_Decoder);
                for (int i = 0; i < wireCases.size(); i++) {
                    Boundary.WireCase v = wireCases.get(i);
                    code.dup();
                    pushInt(code, i);
                    if (TypeOps.caseShape(v.atom(), symbols) == CaseShape.WRAPPED) {
                        code.loadConstant(form.contentsKey());
                        invokeCodec(code, v.atom(), "decoder", MTD_decoder);
                        code.invokestatic(CD_Decoding, "field", MTD_field);
                    } else {
                        invokeCodec(code, v.atom(), "decoder", MTD_decoder);
                    }
                    code.aastore();
                }
                code.invokestatic(CD_Decoding, "discriminate", MTD_discriminate);
                decodeWhatThisWasHanded(code);
                code.areturn();
            });
        });
    }

    /**
     * Decodes a sum all of whose cases are unit data: the value is its case's name, so it reads a
     * bare string and answers that case's singleton.
     *
     * <p>Which names are allowed is held by {@code Decoding.oneOf}, because that states the rule a
     * name is held to — one of these, compared exactly, case and all — so a name no case answers to
     * is refused at the value's path as not one of the names (spec §sum-discrimination). What is the
     * enumeration's own is which case each allowed name is.
     */
    byte[] generateEnumSumDecoder(Hir.SumData sum, Boundary.Alternatives alternatives) {
        ClassDesc cdDec = cd(decoderOf(sum));
        List<Boundary.WireCase> cases = alternatives.wireCases();
        return build(cdDec, cb -> {
            beginCodecClass(cb, CD_Decoder, cdDec);
            // The reader is a constant of the class, built once when it is first used: `oneOf`
            // sorts the names when it is made, which a decode is not to pay for every time.
            cb.withMethodBody(READER, MTD_reader, ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC,
                    code -> {
                code.loadConstant(cases.size());
                code.anewarray(CD_String);
                for (int i = 0; i < cases.size(); i++) {
                    code.dup();
                    code.loadConstant(i);
                    code.loadConstant(cases.get(i).tag());
                    code.aastore();
                }
                code.invokestatic(CD_Decoding, "oneOf", MTD_oneOf);
                code.invokedynamic(fromNameCallSite(cdDec));
                code.invokeinterface(CD_Decoder, "then", MTD_then);
                code.areturn();
            });
            cb.withMethodBody("decode", MTD_decode, ClassFile.ACC_PUBLIC, code -> {
                code.ldc(DynamicConstantDesc.ofNamed(ConstantDescs.BSM_INVOKE, "reader",
                        CD_Decoder, MethodHandleDesc.ofMethod(DirectMethodHandleDesc.Kind.STATIC,
                                cdDec, READER, MTD_reader)));
                decodeWhatThisWasHanded(code);
                code.areturn();
            });
            emitFromNameHelper(cb, cases);
        });
    }

    /**
     * {@code static Result __fromName(String name, Path path)}: the case that name denotes.
     *
     * <p>Handed only a name {@code oneOf} allowed, which is the name of a case. One that is not
     * would be this compiler handing {@code oneOf} other names than it maps, so it throws rather
     * than answering a refusal the language never states.
     */
    private void emitFromNameHelper(ClassBuilder cb, List<Boundary.WireCase> cases) {
        cb.withMethodBody("__fromName", MTD_fromName,
                ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC, code -> {
            for (Boundary.WireCase c : cases) {
                code.loadConstant(c.tag());
                code.aload(0);
                code.invokevirtual(CD_String, "equals", MethodTypeDesc.of(ConstantDescs.CD_boolean, CD_Object));
                Label next = code.newLabel();
                code.ifeq(next);
                loadSharedInstance(code, cd(c.atom()));
                code.invokestatic(CD_Result, "ok", MTD_Result_ok, true);
                code.areturn();
                code.labelBinding(next);
            }
            code.new_(CD_IllegalStateException);
            code.dup();
            code.invokespecial(CD_IllegalStateException, "<init>", MTD_void);
            code.athrow();
        });
    }

    /** What an enumeration's decoder builds the reader it decodes with in, once. */
    private static final String READER = "__reader";

    /** {@code static Decoder __reader()}. */
    private static final MethodTypeDesc MTD_reader = MethodTypeDesc.of(CD_Decoder);

    private static DynamicCallSiteDesc fromNameCallSite(ClassDesc cdDec) {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, cdDec, "__fromName", MTD_fromName);
        return Lambdas.callSite(Lambdas.Sam.STEP, impl, MTD_fromName);
    }

    /** Encodes an enumeration to its case's name — the same string its decoder reads. */
    byte[] generateEnumSumEncoder(Hir.SumData sum) {
        ClassDesc cdEnc = cd(new GeneratedClass.Encoder(valueOf(sum)));
        return build(cdEnc, cb -> {
            beginCodecClass(cb, CD_Encoder, cdEnc);
            cb.withMethodBody("encode", MTD_encode, ClassFile.ACC_PUBLIC, code -> {
                code.aload(1);
                code.invokestatic(cd(sum), TAG_METHOD, MTD_tag, true);
                code.areturn();
            });
        });
    }

    /** Decodes a unit: ignore the input (a unit carries no data) and build the singleton value. */
    byte[] generateUnitDecoder(ClassDesc cdU, ClassDesc cdDec) {
        return build(cdDec, cb -> {
            beginCodecClass(cb, CD_Decoder, cdDec);
            cb.withMethodBody("decode", MTD_decode, ClassFile.ACC_PUBLIC, code -> {
                loadSharedInstance(code, cdU);   // a unit type has exactly one value
                code.invokestatic(CD_Result, "ok", MTD_Result_ok, true);
                code.areturn();
            });
        });
    }

    /** Encodes a unit to an empty Map, the form spec §encoder-derivation gives a unit on its own; a
     *  sum encoder puts the discriminator tag in it, and an enumeration writes the case's name instead. */
    byte[] generateUnitEncoder(ClassDesc cdEnc) {
        return build(cdEnc, cb -> {
            beginCodecClass(cb, CD_Encoder, cdEnc);
            cb.withMethodBody("encode", MTD_encode, ClassFile.ACC_PUBLIC, code -> {
                code.new_(CD_LinkedHashMap);
                code.dup();
                code.invokespecial(CD_LinkedHashMap, "<init>", MTD_void);
                code.areturn();
            });
        });
    }

    /** A data's static {@code decoder()}. */
    void emitDecoderFactory(ClassBuilder cb, Hir.Data data) {
        emitCodecFactory(cb, "decoder", CD_Decoder, cd(decoderOf(data)), decoderSig(cd(data)));
    }

    /** A data's static {@code encoder()}. */
    void emitEncoderFactory(ClassBuilder cb, Hir.Data data) {
        emitCodecFactory(cb, "encoder", CD_Encoder, cd(new GeneratedClass.Encoder(valueOf(data))),
                encoderSig(cd(data), encoderOutput(data)));
    }

    /** Emits a static {@code decoder()}/{@code encoder()} factory returning the shared {@code impl},
     * with a generic {@code Signature} so callers get {@code Decoder<T>} / {@code Encoder<T,..>}
     * rather than a raw type. */
    void emitCodecFactory(ClassBuilder cb, String name, ClassDesc returnIface, ClassDesc impl,
                                  MethodSignature sig) {
        cb.withMethod(name, MethodTypeDesc.of(returnIface),
                ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC, mb -> {
                    mb.with(SignatureAttribute.of(sig));
                    mb.withCode(code -> {
                        loadSharedInstance(code, impl);
                        code.areturn();
                    });
                });
    }

    /** {@code Decoder<T>}: what it reads is the reader's, so the type says only what it builds. */
    static MethodSignature decoderSig(ClassDesc type) {
        return MethodSignature.parseFrom(
                "()Lsouther/runtime/boundary/Decoder<" + type.descriptorString() + ">;");
    }

    /** {@code Encoder<T,O>}: {@code O} is {@code Map<String,Object>} for objects/sums/units, or the
     * bare (boxed) scalar for a newtype — a newtype encodes to a plain value, not a map. */
    static MethodSignature encoderSig(ClassDesc type, ClassDesc output) {
        String out = output.equals(CD_Map)
                ? "Ljava/util/Map<Ljava/lang/String;Ljava/lang/Object;>;"
                : output.descriptorString();
        return MethodSignature.parseFrom(
                "()Lsouther/runtime/boundary/Encoder<" + type.descriptorString() + out + ">;");
    }

    /** The runtime type a data's {@code encode} returns: a {@code Map} for objects/sums, the bare
     * boxed scalar (or {@code Object} for a nested/list/optional value) for a newtype. */
    private ClassDesc encoderOutput(Hir.Data data) {
        return rawOutputType(symbols.derived(data).encoder().result());
    }

    private static ClassDesc rawOutputType(Hir.RawExpr raw) {
        return switch (raw) {
            case Hir.TextRaw _ -> CD_String;
            case Hir.IsoTextRaw _ -> CD_String;
            case Hir.IntRaw _ -> CD_Long;
            case Hir.BoolRaw _ -> CD_Boolean;
            case Hir.DecimalRaw _ -> CD_BigDecimal;
            case Hir.ObjectRaw _ -> CD_Map;
            case Hir.EncodeRaw _ -> CD_Object;
            case Hir.OptionRaw _ -> CD_Object;
            case Hir.ListEnc _ -> CD_Object;
            case Hir.SetEnc _ -> CD_Object;
            case Hir.MapEnc _ -> CD_Object;
        };
    }

    byte[] generateDecoderClass(ClassDesc cdName, Hir.Data data, Hir.DecoderDef dec,
                                        SequencedMap<String, Type> fields) {
        ClassDesc cdDec = cd(decoderOf(data));
        decoderClass = cdDec;
        decodedValue = valueOf(data);
        decodedName = data.name();
        List<ValueShape.Invariant> invariants = invariantsOf(data);
        patternConstants = patternConstantsOf(invariants, data);
        // Every uniqueness of one decoder is about the elements of the one list it decodes, so
        // they are reported in one form and share the helper that writes it.
        List<MessageForm> uniqueElements = constraintsOf(invariants).stream()
                .filter(BoundaryConstraint.Unique.class::isInstance)
                .map(c -> ((BoundaryConstraint.Unique) c).element())
                .distinct().toList();
        if (uniqueElements.size() > 1) {
            throw new IllegalStateException("the elements of one list stated in two forms: "
                    + uniqueElements);
        }
        return build(cdDec, cb -> {
            beginCodecClass(cb, CD_Decoder, cdDec);
            // decode(Object in, Path path, TreeReader reader): this=0, in=1, path=2, reader=3.
            cb.withMethodBody("decode", MTD_decode, ClassFile.ACC_PUBLIC, code -> {
                AstExpressions gen = new AstExpressions(new BodyGen(ctx, code, data, cdName, 4,
                        Places.NUMBERED_NOWHERE));
                switch (dec) {
                    case Hir.PrimDecoder prim -> emitPrimDecode(code, gen, prim, fields, invariants);
                    case Hir.ObjectDecoder obj -> emitObjectDecode(code, gen, obj, fields);
                    case Hir.NewtypeDecoder nt -> emitNewtypeDecode(code, gen, nt, fields, invariants);
                }
            });
            if (!uniqueElements.isEmpty()) {
                UniqueElementForm.emitHelpers(ctx, cb, cdDec, uniqueElements.get(0));
            }
        });
    }

    /**
     * The clauses a decoder checks as the value it decodes: a newtype's, each in the order it is
     * declared, with what it is as constraints — the checker's answer and not this emitter's
     * ({@link ValueShape.Invariant#projection()}).
     *
     * <p>None for a product, which crosses as an object: its fields are decoded one by one and its
     * clauses run whole, as the rules they are, where it is constructed — one field or many, whatever
     * they are as constraints. That is the form a data was declared in deciding how it crosses, and
     * it is asked here, where the crossing is written, and not in the answer.
     */
    private List<ValueShape.Invariant> invariantsOf(Hir.Data data) {
        return data.newtype() ? ctx.shapeOf(data.declares()).invariants() : List.of();
    }

    /** Every constraint the clauses are stated as, for what the decoder class has to carry. */
    private static List<BoundaryConstraint> constraintsOf(List<ValueShape.Invariant> clauses) {
        List<BoundaryConstraint> out = new ArrayList<>();
        for (ValueShape.Invariant clause : clauses) {
            out.addAll(clause.projection().constraints());
        }
        return out;
    }

    private void emitPrimDecode(CodeBuilder code, AstExpressions gen, Hir.PrimDecoder prim,
                                SequencedMap<String, Type> fields,
                                List<ValueShape.Invariant> invariants) {
        Type inputType = prim.from().type();
        Carrier carrier = switch (prim.from()) {
            case STRING -> Carrier.STRING;
            case INT -> Carrier.LONG;
            case DECIMAL -> Carrier.DECIMAL;
            case BOOL, DATE, TIME, DATETIME, INSTANT -> Carrier.PLAIN;
        };
        emitLeafDecoder(code, prim.from());
        emitInvariantConstraints(code, inputType, carrier, invariants);
        emitDecodedOrReturn(code, gen, inputType, prim.input());
        emitConstructCall(code, gen, prim.result(), fields);
    }

    /**
     * A newtype over a non-primitive Y: decode the whole input with Y's decoder, then wrap the
     * result in X (spec §newtype).
     *
     * <p>A map's keys are decoded before any clause is asked: what a clause is about is the map the
     * model declared — its keys converted and canonical — and a key that does not decode is no map
     * of the model's yet, and is refused as that.
     */
    private void emitNewtypeDecode(CodeBuilder code, AstExpressions gen, Hir.NewtypeDecoder dec,
                                   SequencedMap<String, Type> fields,
                                   List<ValueShape.Invariant> invariants) {
        emitDecoderObject(code, dec.inner());
        Carrier carrier = switch (dec.inner()) {
            case Hir.ListDecRef _ -> Carrier.LIST;
            case Hir.MapDecRef _ -> Carrier.MAP;
            default -> Carrier.PLAIN;
        };
        Type innerType = bindType(dec.inner());
        emitInvariantConstraints(code, innerType, carrier, invariants);
        emitDecodedOrReturn(code, gen, innerType, dec.input());
        emitConstructCall(code, gen, dec.result(), fields);
    }

    /**
     * Decodes what this decode was handed with the decoder on the stack, returns its refusals where
     * it refused, and binds what it read to {@code input} otherwise.
     */
    private void emitDecodedOrReturn(CodeBuilder code, AstExpressions gen, Type type, Hir.Binder input) {
        decodeWhatThisWasHanded(code);
        int rSlot = gen.slot(Type.STRING);
        code.astore(rSlot);
        code.aload(rSlot);
        code.instanceOf(CD_ResultErr);
        Label notErr = code.newLabel();
        code.ifeq(notErr);
        code.aload(rSlot);                                            // refused -> as it is
        code.areturn();
        code.labelBinding(notErr);
        code.aload(rSlot);
        code.checkcast(CD_ResultOk);
        code.invokevirtual(CD_ResultOk, "value", MTD_Object);
        int slot = gen.slot(type);
        unbox(code, type, slot);
        gen.bind(input.binding(), input.name(), slot, type);
    }

    /**
     * Decodes an object: whether the node is one is one fact about one node, refused at that node,
     * before any field is read. Without that the fields answer it one at a time — a node of the wrong
     * shape would become one refusal per declared field, and a data whose fields are all optional
     * would decode from it.
     *
     * <p>Every field is read, and every refusal is kept (spec §case-propagation); the value is built
     * only where none was.
     */
    private void emitObjectDecode(CodeBuilder code, AstExpressions gen, Hir.ObjectDecoder obj,
                                  SequencedMap<String, Type> fields) {
        code.aload(1);
        code.aload(2);
        code.aload(3);
        code.invokestatic(CD_Decoding, "notAnObject", MTD_notAnObject);
        code.dup();
        Label anObject = code.newLabel();
        code.ifnull(anObject);
        code.invokestatic(CD_Result, "err", MTD_Result_err, true);
        code.areturn();
        code.labelBinding(anObject);
        code.pop();

        List<Hir.Bind> binds = obj.binds();
        int[] resultSlots = new int[binds.size()];
        for (int i = 0; i < binds.size(); i++) {
            Hir.Bind bind = binds.get(i);
            code.loadConstant(bind.key());
            if (bind.ref() instanceof Hir.OptionDecRef opt) {
                emitDecoderObject(code, opt.element());
                code.invokestatic(CD_Decoding, "optionalField", MTD_field);
            } else {
                emitDecoderObject(code, bind.ref());
                code.invokestatic(CD_Decoding, "field", MTD_field);
            }
            decodeWhatThisWasHanded(code);
            int rSlot = gen.slot(Type.STRING);
            code.astore(rSlot);
            resultSlots[i] = rSlot;
        }

        int accSlot = gen.slot(Type.STRING);
        code.aconst_null();
        code.astore(accSlot);
        for (int i = 0; i < binds.size(); i++) {
            code.aload(resultSlots[i]);
            code.instanceOf(CD_ResultErr);
            Label notErr = code.newLabel();
            code.ifeq(notErr);
            code.aload(accSlot);
            code.aload(resultSlots[i]);
            code.checkcast(CD_ResultErr);
            code.invokevirtual(CD_ResultErr, "error", MTD_error);
            code.checkcast(CD_Refusals);
            code.invokestatic(CD_Decoding, "and", MTD_refusalsAnd);
            code.astore(accSlot);
            code.labelBinding(notErr);
        }
        code.aload(accSlot);
        Label ok = code.newLabel();
        code.ifnull(ok);
        code.aload(accSlot);
        code.invokestatic(CD_Result, "err", MTD_Result_err, true);
        code.areturn();
        code.labelBinding(ok);

        for (int i = 0; i < binds.size(); i++) {
            Hir.Bind bind = binds.get(i);
            Type t = bindType(bind.ref());
            code.aload(resultSlots[i]);
            code.checkcast(CD_ResultOk);
            code.invokevirtual(CD_ResultOk, "value", MTD_Object);
            int vSlot = gen.slot(t);
            unbox(code, t, vSlot);
            gen.bind(bind.binder().binding(), bind.binder().name(), vSlot, t);
        }
        emitConstructCall(code, gen, obj.result(), fields);
    }

    private Type bindType(Hir.DecRef ref) {
        return switch (ref) {
            case Hir.PrimDecRef p -> p.kind().type();
            case Hir.DataDecRef d -> Type.ref(Backend.names(d.typeName()));
            case Hir.ListDecRef l -> Type.list(bindType(l.element()));
            case Hir.SetDecRef s -> Type.set(bindType(s.element()));
            case Hir.OptionDecRef o -> Type.option(bindType(o.element()));
            case Hir.MapDecRef mp -> Type.map(mp.key().type(), bindType(mp.value()));
        };
    }

    /** Pushes a {@code Decoder} for the given field-value reference. */
    private void emitDecoderObject(CodeBuilder code, Hir.DecRef ref) {
        switch (ref) {
            case Hir.PrimDecRef p -> emitLeafDecoder(code, p.kind());
            case Hir.DataDecRef d -> invokeCodec(code, d.typeName(), "decoder", MTD_decoder);
            case Hir.ListDecRef l -> {
                emitDecoderObject(code, l.element());
                code.invokestatic(CD_Decoding, "list", MTD_wrapDecoder);
            }
            case Hir.SetDecRef s -> {
                emitDecoderObject(code, s.element());
                code.invokestatic(CD_Decoding, "list", MTD_wrapDecoder);       // Decoder<List<T>>
                code.invokedynamic(setFromListCallSite());                    // Function: List -> Set
                code.invokeinterface(CD_Decoder, "map", MTD_decoderMap);      // Decoder<Set<T>> (dedup)
            }
            // An optional standing where there is no key to be missing — a member, a map's value.
            // There null is the whole of what absence is (spec [#absence-is-written-as-null]). A
            // field's optional never reaches here: its key is read by `optionalField` instead.
            case Hir.OptionDecRef o -> {
                emitDecoderObject(code, o.element());
                code.invokestatic(CD_Decoding, "nullable", MTD_wrapDecoder);
            }
            // Every boundary map's keys are decoded into the key type: a text key is canonicalized,
            // a temporal's parsed, a named key's own decoder run. Two source keys that are one key
            // once decoded are refused, since a map would otherwise lose one value to the other.
            case Hir.MapDecRef mp -> {
                emitDecoderObject(code, mp.value());
                code.invokestatic(CD_Decoding, "map", MTD_wrapDecoder);        // Decoder<Map<String,V>>
                emitKeyDecoder(code, mp.key());
                code.invokestatic(CD_Decoding, "keys", MTD_keys);
                code.invokeinterface(CD_Decoder, "then", MTD_then);            // Decoder<Map<K,V>>
            }
        }
    }

    /**
     * What a newtype's clauses are stated of, which is what decides which constraints can be stated
     * of it. A constraint stated of another kind of value is this compiler's mistake.
     */
    private enum Carrier {
        STRING, LONG, DECIMAL, LIST,
        /** The map the model declares, its keys decoded. */
        MAP,
        /** Any other value, of which nothing but a clause's own check is stated. */
        PLAIN
    }

    /**
     * Constrains the decoder on the stack with the newtype's invariant, clause by clause in the order
     * they are declared. What the checker found a clause to be as constraints
     * ({@link ConstraintProjection}) is chained as those constraints, so the refusal says the
     * constraint and its data at the value's path rather than one clause refusal for every rule in
     * the model. Where they are not the whole clause, the clause's own check follows them, refusing
     * with the clause itself.
     *
     * <p>The first refusal stops the rest, so the chain's order is the order a refusal is reported
     * in — the same order {@code __construct} decides in, so the boundary and an attempted
     * construction name the same clause for the same value.
     */
    private void emitInvariantConstraints(CodeBuilder code, Type base, Carrier carrier,
                                          List<ValueShape.Invariant> clauses) {
        for (int i = 0; i < clauses.size(); i++) {
            ValueShape.Invariant clause = clauses.get(i);
            for (BoundaryConstraint c : clause.projection().constraints()) {
                emitConstraint(code, carrier, c);
            }
            if (!clause.projection().complete()) {
                code.invokedynamic(invariantPredicateCallSite(base, i));
                emitInvariantFailure(code, clause);
                code.invokestatic(CD_Decoding, "clause", MTD_clause);
            }
        }
    }

    /**
     * Pushes the {@code InvariantFailure} a clause refuses with: the rejecting type, the clause's
     * name where it has one, and which clause it is — the declaration that wrote it and its place
     * there. The same value {@code __construct} hands its caller, so the boundary and an abort say
     * the same thing about the same failure.
     */
    private void emitInvariantFailure(CodeBuilder code, ValueShape.Invariant clause) {
        code.new_(CD_InvariantFailure);
        code.dup();
        code.loadConstant(ctx.module());
        code.loadConstant(decodedName);
        if (clause.name().isPresent()) {
            code.loadConstant(clause.name().get());
        } else {
            code.aconst_null();
        }
        code.new_(CD_InvariantFailureDeclared);
        code.dup();
        code.loadConstant(clause.declaredOn().module());
        code.loadConstant(clause.declaredOn().name());
        code.loadConstant(clause.ordinal());
        code.invokespecial(CD_InvariantFailureDeclared, "<init>", MethodTypeDesc.of(
                ConstantDescs.CD_void, CD_String, CD_String, ConstantDescs.CD_int));
        code.invokespecial(CD_InvariantFailure, "<init>", MethodTypeDesc.of(
                ConstantDescs.CD_void, CD_String, CD_String, CD_String,
                CD_InvariantFailureDeclared));
    }

    private void emitConstraint(CodeBuilder code, Carrier carrier, BoundaryConstraint c) {
        Carrier about = switch (c) {
            case BoundaryConstraint.OfString _ -> Carrier.STRING;
            case BoundaryConstraint.OfInt _ -> Carrier.LONG;
            case BoundaryConstraint.OfDecimal _ -> Carrier.DECIMAL;
            case BoundaryConstraint.OfList _ -> Carrier.LIST;
            case BoundaryConstraint.OfMap _ -> Carrier.MAP;
        };
        if (about != carrier) {
            throw new IllegalStateException("a constraint on a value decoded by " + about
                    + " was stated of one decoded by " + carrier + ": " + c);
        }
        switch (c) {
            case BoundaryConstraint.MinLength m -> intBound(code, "minLength", m.n());
            case BoundaryConstraint.MaxLength m -> intBound(code, "maxLength", m.n());
            case BoundaryConstraint.FixedLength f -> intBound(code, "length", f.n());
            case BoundaryConstraint.Pattern p -> {
                // The machine is a constant of the class, built once when it is first loaded. What a
                // refusal quotes is the pattern the call was given.
                DynamicConstantDesc<Object> machine = patternConstants.get(p.meaning());
                if (machine == null) {
                    throw new IllegalStateException(
                            "a pattern the decoder class holds no constant for: " + p);
                }
                code.ldc(machine);
                code.loadConstant(p.written());
                code.invokestatic(CD_Decoding, "pattern", MTD_pattern);
            }
            case BoundaryConstraint.Min m -> {
                code.loadConstant(m.n());
                code.invokestatic(CD_Decoding, "min", MTD_longBound);
            }
            case BoundaryConstraint.Max m -> {
                code.loadConstant(m.n());
                code.invokestatic(CD_Decoding, "max", MTD_longBound);
            }
            case BoundaryConstraint.Positive _ -> unbounded(code, "positive");
            case BoundaryConstraint.NonNegative _ -> unbounded(code, "nonNegative");
            case BoundaryConstraint.DecimalMin m -> {
                emitBigDecimal(code, m.n());
                code.invokestatic(CD_Decoding, "decimalMin", MTD_decimalBound);
            }
            case BoundaryConstraint.DecimalMax m -> {
                emitBigDecimal(code, m.n());
                code.invokestatic(CD_Decoding, "decimalMax", MTD_decimalBound);
            }
            case BoundaryConstraint.DecimalPositive _ -> unbounded(code, "decimalPositive");
            case BoundaryConstraint.DecimalNonNegative _ -> unbounded(code, "decimalNonNegative");
            case BoundaryConstraint.NonEmpty _ -> unbounded(code, "nonEmpty");
            case BoundaryConstraint.MinSize m -> intBound(code, "minSize", m.n());
            case BoundaryConstraint.MaxSize m -> intBound(code, "maxSize", m.n());
            case BoundaryConstraint.FixedSize f -> intBound(code, "size", f.n());
            case BoundaryConstraint.Unique _ -> {
                UniqueElementForm.push(code, decoderClass);
                code.invokestatic(CD_Decoding, "unique", MTD_unique);
            }
            case BoundaryConstraint.MapNonEmpty _ -> unbounded(code, "nonEmpty");
            case BoundaryConstraint.MapMinSize m -> intBound(code, "minSize", m.n());
            case BoundaryConstraint.MapMaxSize m -> intBound(code, "maxSize", m.n());
        }
    }

    private static void intBound(CodeBuilder code, String constraint, int bound) {
        pushInt(code, bound);
        code.invokestatic(CD_Decoding, constraint, MTD_intBound);
    }

    private static void unbounded(CodeBuilder code, String constraint) {
        code.invokestatic(CD_Decoding, constraint, MTD_wrapDecoder);
    }

    private static void emitBigDecimal(CodeBuilder code, BigDecimal value) {
        code.new_(CD_BigDecimal);
        code.dup();
        code.loadConstant(value.toString());
        code.invokespecial(CD_BigDecimal, "<init>", MethodTypeDesc.of(ConstantDescs.CD_void, CD_String));
    }

    /** {@code invokedynamic} producing a {@code Predicate} over the type's {@code $Ctfe.check$i} — the
     * clause declared {@code i}th as a plain boolean, emitted beside the whole-invariant check
     * compile-time construction checking uses (ADR-0032). */
    private DynamicCallSiteDesc invariantPredicateCallSite(Type base, int clause) {
        ClassDesc cdCtfe = cd(new GeneratedClass.Ctfe(decodedValue));
        MethodTypeDesc check = MethodTypeDesc.of(ConstantDescs.CD_boolean, JvmTypes.jvmType(base, ctx));
        // A Predicate's argument is a reference, so the instantiated type takes the decoded value's
        // boxed form and the metafactory unboxes it into `check`'s primitive parameter.
        ClassDesc boxed = JvmTypes.boxedPrim(base) != null ? JvmTypes.boxedPrim(base)
                : JvmTypes.jvmType(base, ctx);
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, cdCtfe,
                ValueClassGen.ctfeClauseCheck(clause), check);
        return Lambdas.callSite(Lambdas.Sam.PREDICATE, impl,
                MethodTypeDesc.of(ConstantDescs.CD_boolean, boxed));
    }

    /**
     * Each pattern the clauses are stated as, by what it matches, with the constant its machine is
     * loaded from.
     *
     * <p>Worked out before the decode method is written, so a pattern this backend writes no machine
     * for is refused at the data that states it rather than partway through the class. A refusal is
     * reported at the declaration: the constraint was read off its clauses and holds no place of its
     * own.
     */
    private Map<PatternMeaning, DynamicConstantDesc<Object>> patternConstantsOf(
            List<ValueShape.Invariant> invariants, Hir.Data data) {
        Map<PatternMeaning, DynamicConstantDesc<Object>> out = new LinkedHashMap<>();
        for (BoundaryConstraint c : constraintsOf(invariants)) {
            if (c instanceof BoundaryConstraint.Pattern p && !out.containsKey(p.meaning())) {
                out.put(p.meaning(), ctx.patterns.of(p.meaning(), p.written(),
                        Diagnostic.at(data.written().reportedAt())));
            }
        }
        return out;
    }

    /**
     * Emits the {@code __construct} call for a decoded value, and answers what it answers: the value,
     * or the clause it broke as a refusal at the value's path (spec §violation-destination,
     * §decoder-role). Must be emitted inside a decode body: it reads the path from slot 2.
     */
    private void emitConstructCall(CodeBuilder code, AstExpressions gen, Hir.Construct construct,
                                   SequencedMap<String, Type> fields) {
        // The decoder is still AST-level; elaborate its field inits so the shared emitFieldValues
        // consumes one representation, with the type the checker decides for each (ADR-0021).
        // The field's declared type is pushed in, as the checker does when it checks a construction.
        // a decoder's construction gives every field a value of its own, and they are put in
        // declaration order here as a construction in a body already holds them
        Map<String, Hir.FieldInit> written = new HashMap<>();
        for (Hir.FieldInit init : construct.inits()) {
            written.put(init.name(), init);
        }
        List<Core.FieldValue> values = new ArrayList<>();
        for (String field : fields.keySet()) {
            Hir.FieldInit init = written.get(field);
            values.add(new Core.FieldValue(field,
                    gen.elaborate(init.value(), fields.get(field)), init.pos()));
        }
        gen.emitFieldValues(fields, values);
        if (!(Backend.names(construct.typeName()) instanceof TypeSymbol.AtModule built)) {
            throw new IllegalStateException("a decoder builds `" + construct.typeName()
                    + "`, which no module declares");
        }
        CodegenContext.invoke(code, ctx.construction(built));
        int srSlot = gen.slot(Type.STRING);
        code.astore(srSlot);
        code.aload(srSlot);
        code.instanceOf(CD_ResultErr);
        Label okL = code.newLabel();
        code.ifeq(okL);
        code.aload(srSlot);
        code.checkcast(CD_ResultErr);
        code.invokevirtual(CD_ResultErr, "error", MTD_error);
        code.checkcast(CD_InvariantFailure);
        // the path this value was decoded at (spec §violation-destination, §case-propagation) —
        // not the document root
        code.aload(2);
        code.invokestatic(CD_Decoding, "refusedBy", MTD_refusedBy);
        code.areturn();
        code.labelBinding(okL);
        code.aload(srSlot);                                     // the value, already a Result
        code.areturn();
    }

    byte[] generateEncoderClass(ClassDesc cdName, Hir.Data data, Hir.EncoderDef enc) {
        ClassDesc cdEnc = cd(new GeneratedClass.Encoder(valueOf(data)));
        return build(cdEnc, cb -> {
            beginCodecClass(cb, CD_Encoder, cdEnc);
            cb.withMethodBody("encode", MTD_encode, ClassFile.ACC_PUBLIC, code -> {
                AstExpressions gen = new AstExpressions(new BodyGen(ctx, code, data, cdName, 2,
                        Places.NUMBERED_NOWHERE));
                code.aload(1);
                code.checkcast(cdName);
                int selfSlot = gen.slot(Type.ref(data.declares()));
                code.astore(selfSlot);
                gen.bind(enc.self().binding(), enc.self().name(), selfSlot, Type.ref(data.declares()));
                emitRawExpr(code, gen, enc.result());
                code.areturn();
            });
        });
    }

    private void emitRawExpr(CodeBuilder code, AstExpressions gen, Hir.RawExpr raw) {
        switch (raw) {
            case Hir.TextRaw t -> gen.expr(t.arg());                 // String is a neutral value
            case Hir.IntRaw i -> {
                gen.expr(i.arg());
                box(code, Type.INT);                                 // long -> Long
            }
            case Hir.BoolRaw b -> {
                gen.expr(b.arg());
                box(code, Type.BOOL);                                // boolean -> Boolean
            }
            case Hir.DecimalRaw d -> {
                gen.expr(d.arg());                                   // BigDecimal is neutral
                ctx.callRuntime(code, CD_Representations, "canonicalNumber", MTD_canonicalNumber,
                        Work.CHECKPOINTED);
            }
            case Hir.IsoTextRaw t -> {
                gen.expr(t.arg());
                code.invokevirtual(CD_Object, "toString", MethodTypeDesc.of(CD_String));
            }
            case Hir.EncodeRaw e -> {
                invokeCodec(code, e.typeName(), "encoder", MTD_encoder);
                gen.expr(e.arg());
                code.invokeinterface(CD_Encoder, "encode", MTD_encode);
            }
            case Hir.OptionRaw o -> {
                Type at = gen.expr(o.access());            // Option on the stack
                Type elemType = ((Type.OptionOf) at).element();
                code.dup();
                code.instanceOf(CD_OptionNone);
                Label none = code.newLabel();
                Label end = code.newLabel();
                code.ifne(none);
                code.checkcast(CD_OptionSome);
                code.invokevirtual(CD_OptionSome, "value", MTD_Object);
                int slot = gen.slot(elemType);
                unbox(code, elemType, slot);
                gen.bind(o.elem().binding(), o.elem().name(), slot, elemType);
                emitRawExpr(code, gen, o.inner());          // Some(v) -> encode v
                code.goto_(end);
                code.labelBinding(none);
                code.pop();                                 // discard the None value
                code.aconst_null();                         // null in the neutral tree
                code.labelBinding(end);
            }
            case Hir.ListEnc le -> {
                pushElemEncoder(code, le.elem());
                code.invokestatic(CD_Encoding, "list", MTD_wrapEncoder);
                gen.expr(le.source());
                code.invokeinterface(CD_Encoder, "encode", MTD_encode);
            }
            case Hir.SetEnc se -> {
                pushElemEncoder(code, se.elem());
                code.invokestatic(CD_Encoding, "list", MTD_wrapEncoder);       // Encoder for an array
                gen.expr(se.source());                                          // the Set value
                ctx.callRuntime(code, CD_Sets, "toList", MethodTypeDesc.of(CD_List, CD_Set),   // Set -> List
                        Work.CHECKPOINTED);
                code.invokeinterface(CD_Encoder, "encode", MTD_encode);        // encode the array
                ctx.callRuntime(code, CD_Representations, "sortedArray", MTD_Representations_sorted,
                        Work.CHECKPOINTED);
            }
            case Hir.MapEnc me -> {
                pushElemEncoder(code, me.elem());
                code.invokestatic(CD_Encoding, "map", MTD_wrapEncoder);        // Encoder<Map<String,V>,Object>
                gen.expr(me.source());                                          // Map<K,V>
                if (needsKeyRender(me.key())) {
                    // Render the keys bare before the String-keyed map encoder.
                    pushKeyRenderer(code, me.key());                            // Function<K,String>
                    ctx.callRuntime(code, CD_Maps, "mapKeys", MTD_mapKeys, Work.CHECKPOINTED);   // Map<String,V>
                }
                code.invokeinterface(CD_Encoder, "encode", MTD_encode);
                ctx.callRuntime(code, CD_Representations, "sortedObject", MTD_Representations_sorted,
                        Work.CHECKPOINTED);
            }
            case Hir.ObjectRaw o -> {
                code.new_(CD_LinkedHashMap);
                code.dup();
                code.invokespecial(CD_LinkedHashMap, "<init>", MTD_void);
                for (Hir.RawEntry entry : o.entries()) {
                    if (entry.value() instanceof Hir.OptionRaw opt) {
                        emitOptionalEntry(code, gen, entry.key(), opt);
                        continue;
                    }
                    code.dup();
                    code.loadConstant(entry.key());
                    emitRawExpr(code, gen, entry.value());
                    code.invokeinterface(CD_Map, "put", MTD_Map_put);
                    code.pop();
                }
                // the LinkedHashMap is itself the neutral object value
            }
        }
    }

    /**
     * Puts an optional field into the object map only when it is {@code Some}: {@code None} omits
     * the key entirely rather than writing {@code null} (spec §encoder-derivation). The map is on the stack on
     * entry and left on the stack on exit, so both the Some and None branches converge on it.
     */
    private void emitOptionalEntry(CodeBuilder code, AstExpressions gen, String key, Hir.OptionRaw o) {
        Type at = gen.expr(o.access());                 // map, opt
        Type elemType = ((Type.OptionOf) at).element();
        code.dup();                                     // map, opt, opt
        code.instanceOf(CD_OptionNone);                 // map, opt, isNone
        Label none = code.newLabel();
        Label end = code.newLabel();
        code.ifne(none);                                // map, opt
        code.checkcast(CD_OptionSome);
        code.invokevirtual(CD_OptionSome, "value", MTD_Object);   // map, valueObj
        int slot = gen.slot(elemType);
        unbox(code, elemType, slot);                    // map (value bound to local)
        gen.bind(o.elem().binding(), o.elem().name(), slot, elemType);
        code.dup();                                     // map, map
        code.loadConstant(key);                         // map, map, key
        emitRawExpr(code, gen, o.inner());              // map, map, key, encoded
        code.invokeinterface(CD_Map, "put", MTD_Map_put);
        code.pop();                                     // map
        code.goto_(end);
        code.labelBinding(none);                        // map, opt
        code.pop();                                     // map (drop the None, write nothing)
        code.labelBinding(end);
    }

    /** Pushes an {@code Encoder} for a list/set/map element. A nested collection composes the same
     * parts the field encoders use, so a {@code Map<String, List<商品ID>>} encodes as
     * {@code map(list(商品ID.encoder()))}. Set and newtype-keyed Map have no encoder of their own —
     * they are the list / String-keyed map encoder with the value converted first, which
     * {@code contramap} does. */
    private void pushElemEncoder(CodeBuilder code, Hir.EncElem elem) {
        switch (elem) {
            case Hir.PrimEnc p -> {
                code.invokestatic(CD_Encoding, leafName(p.kind()), MTD_encoder);
                canonicalizeAmount(code, p.kind());
            }
            case Hir.DataEnc d -> invokeCodec(code, d.typeName(), "encoder", MTD_encoder);
            case Hir.ListElemEnc l -> {
                pushElemEncoder(code, l.elem());
                code.invokestatic(CD_Encoding, "list", MTD_wrapEncoder);
            }
            case Hir.SetElemEnc s -> {
                pushElemEncoder(code, s.elem());
                code.invokestatic(CD_Encoding, "list", MTD_wrapEncoder);
                code.invokedynamic(setToListCallSite());                    // Function<Set, List>
                code.invokeinterface(CD_Encoder, "contramap", MTD_encoderContramap);
                code.invokedynamic(orderingCallSite("sortedArray"));        // Encoder<Object, Object>
                code.invokeinterface(CD_Encoder, "andThen", MTD_encoderAndThen);
            }
            // no key to omit here, so an absent member is written null
            case Hir.OptionElemEnc o -> {
                pushElemEncoder(code, o.elem());                            // Encoder<T, Object>
                code.invokedynamic(encodeAsFunctionCallSite());             // Function<T, Object>
                code.invokedynamic(optionElemEncoderCallSite());            // Encoder<Option<T>, Object>
            }
            case Hir.MapElemEnc m -> {
                pushElemEncoder(code, m.value());
                code.invokestatic(CD_Encoding, "map", MTD_wrapEncoder);
                if (needsKeyRender(m.key())) {
                    pushKeyRenderer(code, m.key());                         // Function<K, String>
                    code.invokedynamic(mapKeysCallSite());                  // Function<Map<K,V>, Map<String,V>>
                    code.invokeinterface(CD_Encoder, "contramap", MTD_encoderContramap);
                }
                code.invokedynamic(orderingCallSite("sortedObject"));       // Encoder<Object, Object>
                code.invokeinterface(CD_Encoder, "andThen", MTD_encoderAndThen);
            }
        }
    }

    /**
     * A leaf encoder for a {@code Decimal}, followed by the amount's own form. The leaf hands the
     * {@code BigDecimal} through as it is, scale and all, and the scale is how a number was written
     * rather than how much it is.
     */
    private void canonicalizeAmount(CodeBuilder code, LeafScalar kind) {
        if (kind != LeafScalar.DECIMAL) {
            return;
        }
        code.invokedynamic(canonicalNumberCallSite());
        code.invokeinterface(CD_Encoder, "andThen", MTD_encoderAndThen);
    }

    /** {@code Representations::canonicalNumber} as an {@code Encoder}. */
    private DynamicCallSiteDesc canonicalNumberCallSite() {
        DirectMethodHandleDesc impl = ctx.boundRuntime(CD_Representations, "canonicalNumber",
                MTD_canonicalNumber, Work.CHECKPOINTED);
        return Lambdas.callSite(Lambdas.Sam.ENCODER, impl, MTD_canonicalNumber);
    }

    /**
     * {@code Representations::sortedArray} / {@code ::sortedObject} as an {@code Encoder}, so a
     * nested collection is put in order after its members have been encoded.
     *
     * <p>The field-level arms above call the same method directly, on the value the encode left on
     * the stack. Both are here rather than in one place after the fact because this is the last
     * point at which the type is still known: once encoded, a Set and a List are both a
     * {@code java.util.List}, and only one of the two may be reordered.
     */
    private DynamicCallSiteDesc orderingCallSite(String ordering) {
        DirectMethodHandleDesc impl = ctx.boundRuntime(CD_Representations, ordering,
                MTD_Representations_sorted, Work.CHECKPOINTED);
        return Lambdas.callSite(Lambdas.Sam.ENCODER, impl, MTD_Representations_sorted);
    }

    /** An {@code Encoder}'s own {@code encode} as a {@code Function}, capturing the encoder already
     *  on the stack. The kernel does not know the boundary's types, so what it is handed is a
     *  function rather than an encoder ({@code Options.encodedOrNull}). */
    private static DynamicCallSiteDesc encodeAsFunctionCallSite() {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.INTERFACE_VIRTUAL, CD_Encoder, "encode", MTD_encode);
        return Lambdas.callSite(Lambdas.Sam.FUNCTION, impl, MTD_encode,
                CD_Encoder);                                             // captures the encoder
    }

    /** {@code opt -> Options.encodedOrNull(inner, opt)} as an {@code Encoder}, capturing the present
     *  value's encoder as a function: an absent member is written null. */
    private static DynamicCallSiteDesc optionElemEncoderCallSite() {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, CD_Options, "encodedOrNull", MTD_encodedOrNull);
        return Lambdas.callSite(Lambdas.Sam.ENCODER, impl, MethodTypeDesc.of(CD_Object, CD_Option),
                CD_Function);                                            // captures the function
    }

    /** {@code Sets::toList} as a {@code Function}, so a nested Set reaches the list encoder. */
    private DynamicCallSiteDesc setToListCallSite() {
        DirectMethodHandleDesc impl = ctx.boundRuntime(CD_Sets, "toList", MTD_Sets_toList, Work.CHECKPOINTED);
        return Lambdas.callSite(Lambdas.Sam.FUNCTION, impl, MTD_Sets_toList);
    }

    /** {@code m -> Maps.mapKeysWith(keyFn, m)} as a {@code Function}, capturing the key function
     * already on the stack: a nested newtype-keyed Map renders its keys bare before the String-keyed
     * map encoder sees it. */
    private DynamicCallSiteDesc mapKeysCallSite() {
        DirectMethodHandleDesc impl = ctx.boundRuntime(CD_Maps, "mapKeysWith", MTD_mapKeysWith,
                Work.CHECKPOINTED);
        return Lambdas.callSite(Lambdas.Sam.FUNCTION, impl, MethodTypeDesc.of(CD_Map, CD_Map),
                CD_Function);                                            // captures the key Function
    }

    // --- a behavior output union's encoder (spec §jvm-anonymous-union) -------------------------------------------

    /**
     * The encoder of a behavior's anonymous output union: dispatch on the member, encode it as that
     * member writes itself, and write the discriminator under the keys of the form it was handed —
     * what a named sum over the same leaves does (spec §encoder-derivation). Without it the same value would travel two ways depending on
     * where it sat, since a member's own encoder writes no discriminator.
     *
     * <p>A member this module declared is the case itself; any other arrives in its bridge case, and
     * the value is read out of that before its own encoder sees it. The bridge case still carries no
     * codec of its own — belonging to a union does not change a member's external representation,
     * only what wraps it here.
     */
    byte[] generateResultUnionEncoder(GeneratedClass.BehaviorResult union,
                                     Boundary.Alternatives alternatives) {
        ClassDesc cdEnc = cd(new GeneratedClass.Encoder(union));
        boolean enumeration =
                alternatives.representation() instanceof Boundary.Representation.Enumeration;
        Boundary.Representation.Discriminated form = enumeration ? null : discriminated(alternatives);
        return build(cdEnc, cb -> {
            beginCodecClass(cb, CD_Encoder, cdEnc);
            cb.withMethodBody("encode", MTD_encode, ClassFile.ACC_PUBLIC, code -> {
                for (Boundary.WireCase member : alternatives.wireCases()) {
                    Label next = code.newLabel();
                    code.aload(1);
                    code.instanceOf(ctx.resultMemberClass(member.atom()));
                    code.ifeq(next);
                    if (enumeration) {
                        code.loadConstant(member.tag());
                    } else {
                        emitMemberEncode(code, member, form);
                    }
                    code.areturn();
                    code.labelBinding(next);
                }
                code.new_(CD_IllegalStateException);
                code.dup();
                code.invokespecial(CD_IllegalStateException, "<init>", MTD_void);
                code.athrow();
            });
        });
    }

    /** Leaves the member on the stack encoded and tagged, the value in slot 1. */
    private void emitMemberEncode(CodeBuilder code, Boundary.WireCase member,
                                  Boundary.Representation.Discriminated form) {
        emitTagged(code, TypeOps.caseShape(member.atom(), symbols), form, member.tag(), () -> {
            pushMemberEncoder(code, member.atom());
            pushMemberValue(code, member.atom());
            code.invokeinterface(CD_Encoder, "encode", MTD_encode);
        });
    }

    /**
     * Leaves a discriminated case on the stack: what the case writes on its own, plus what standing
     * in this sum — or in a behavior's answer, which is the same rule — adds to it (spec §encoder-derivation). A
     * product lays its fields beside the discriminator and a unit is the discriminator alone, so both
     * carry it in the object membership gives them; a newtype and a primitive are wrapped, so their
     * standalone representation goes unchanged under the form's contents key beside it — a newtype
     * over a record included, although that representation is an object. {@code shape} picks which
     * of the two and is read from the declaration; every key written comes from {@code form}.
     *
     * @param encoded leaves the case's own encoded form on the stack
     */
    private void emitTagged(CodeBuilder code, CaseShape shape,
                            Boundary.Representation.Discriminated form, String tag, Runnable encoded) {
        switch (shape) {
            case PRODUCT, UNIT -> {
                encoded.run();
                code.checkcast(CD_Map);
                code.dup();
                code.loadConstant(form.tagKey());
                code.loadConstant(tag);
                code.invokeinterface(CD_Map, "put", MTD_Map_put);
                code.pop();
            }
            case WRAPPED -> {
                code.new_(CD_LinkedHashMap);
                code.dup();
                code.invokespecial(CD_LinkedHashMap, "<init>", MTD_void);
                code.dup();
                code.loadConstant(form.tagKey());
                code.loadConstant(tag);
                code.invokeinterface(CD_Map, "put", MTD_Map_put);
                code.pop();
                code.dup();
                code.loadConstant(form.contentsKey());
                encoded.run();
                code.invokeinterface(CD_Map, "put", MTD_Map_put);
                code.pop();
            }
        }
    }

    /** Pushes the encoder a member writes itself with: its own derived one, or the leaf encoder for
     * a primitive, which declares none. */
    private void pushMemberEncoder(CodeBuilder code, TypeSymbol member) {
        if (member.isPrimitive()) {
            LeafScalar scalar = memberScalar(member);
            code.invokestatic(CD_Encoding, leafName(scalar), MTD_encoder);
            canonicalizeAmount(code, scalar);
            return;
        }
        // a member is one of the union's effective members, every named sum already expanded to its
        // leaves (spec §jvm-product), so its encoder() is on a class and never on a sealed interface
        code.invokestatic(cd(member), "encoder", MTD_encoder, false);
    }

    /** Pushes the Souther value the member holds: the union value itself for a member this module
     * declared, and what the bridge case wraps for any other. */
    private void pushMemberValue(CodeBuilder code, TypeSymbol member) {
        code.aload(1);
        if (ctx.isLocalMember(member)) {
            return;
        }
        ClassDesc bridge = ctx.bridgeCaseClass(member);
        Type held = TypeOps.caseBindType(member);
        code.checkcast(bridge);
        code.invokevirtual(bridge, "value", MethodTypeDesc.of(JvmTypes.jvmType(held, ctx)));
        JvmTypes.box(code, held);
    }

    /** The static {@code encoder()} factory on the union's sealed interface. */
    void emitResultUnionEncoderFactory(ClassBuilder cb, GeneratedClass.BehaviorResult union,
                                       Boundary.Alternatives alternatives) {
        boolean enumeration =
                alternatives.representation() instanceof Boundary.Representation.Enumeration;
        emitCodecFactory(cb, "encoder", CD_Encoder, cd(new GeneratedClass.Encoder(union)),
                encoderSig(cd(union), enumeration ? CD_String : CD_Map));
    }

    /**
     * The discriminated form the alternatives travel in, with the keys it writes them under.
     *
     * <p>Asked of the settled representation rather than written here. An enumeration has no keys —
     * the value is the tag — so a caller reaching this for one is asking about a form it does not
     * have, and that is a mistake in the caller rather than a key to invent.
     */
    private static Boundary.Representation.Discriminated discriminated(Boundary.Alternatives alternatives) {
        return switch (alternatives.representation()) {
            case Boundary.Representation.Discriminated d -> d;
            case Boundary.Representation.Enumeration _ -> throw new IllegalStateException(
                    "an enumeration travels as its tag and writes it under no key");
        };
    }

    /**
     * The scalar a primitive member is. Recovered through {@link TypeSymbol#primitiveKind()}, which is
     * the inverse of the mint a primitive case name comes from, rather than through a table of
     * spellings kept here — that table was a second place for the language's own spelling to be
     * written, and it answered a member outside it by raising.
     */
    private static LeafScalar memberScalar(TypeSymbol member) {
        Type.Prim prim = member.primitiveKind();
        LeafScalar scalar = prim == null ? null : LeafScalar.of(prim);
        if (scalar == null) {
            throw new IllegalStateException("`" + member + "` is a member of a behavior's answer and"
                    + " names no scalar a leaf codec exists for");
        }
        return scalar;
    }

    /** The {@code Decoding} and {@code Encoding} leaf of each scalar: one name for both, so a leaf
     *  decoder and its encoder cannot be two scalars. */
    private static String leafName(LeafScalar kind) {
        return switch (kind) {
            case STRING -> "string";
            case INT -> "integer";
            case BOOL -> "bool";
            case DECIMAL -> "decimal";
            case DATE -> "date";
            case TIME -> "time";
            case DATETIME -> "dateTime";
            case INSTANT -> "instant";
        };
    }

    /**
     * An AST expression emitted through the checker.
     *
     * <p>The one AST-level path this backend has, and the whole of it. A decoder and an encoder are
     * still written as AST when they reach here (ADR-0021), so their expressions are typed at the
     * environment the slots hold and emitted from what that produced; everything else the backend
     * emits — a body, a data's invariant, a behavior's rule — arrives as the Core the checker made,
     * and {@link BodyGen} has no way in from an AST at all.
     *
     * <p>Here rather than beside the emitter it uses, so that what may turn an AST into Core inside
     * this package is one type in one file, and adding a second is a thing somebody has to write
     * rather than a method already in reach ({@code
     * souther.compiler.codegen.OnlyTheCodecEmitterTurnsAnAstIntoCoreTest}).
     */
    private static final class AstExpressions {

        private final BodyGen body;

        AstExpressions(BodyGen body) {
            this.body = body;
        }

        /** Emits an AST expression: elaborated here, and emitted from what that produced. */
        Type expr(Hir.Expr e) {
            return body.genExpr(elaborate(e, null));
        }

        /**
         * Elaborates an AST expression at this body's environment. It is desugared first, by the
         * same rewrite a body gets, so a surface form with no Core node of its own (a comprehension)
         * reaches the emitter in the shape it emits from. {@code expected} is the type the position
         * wants, as the checker pushes a field's declared type into its initialiser.
         */
        Core elaborate(Hir.Expr e, Type expected) {
            return Elaborator.elaborate(Lower.desugarExpr(e), body.scope(), body.context(), expected);
        }

        int slot(Type type) {
            return body.slot(type);
        }

        void bind(BindingId binding, String name, int slot, Type type) {
            body.bind(binding, name, slot, type);
        }

        void emitFieldValues(Map<String, Type> fields, List<Core.FieldValue> values) {
            body.emitFieldValues(fields, values);
        }
    }
}
