package souther.compiler.codegen;

import souther.compiler.check.Boundary;
import souther.compiler.check.Elaborator;
import souther.compiler.check.Lower;
import souther.compiler.check.Derived;
import souther.compiler.check.DerivedSymbols;
import souther.compiler.ast.Hir;
import souther.compiler.core.BoundaryConstraint;
import souther.compiler.core.ConstraintProjection;
import souther.compiler.core.ValueShape;
import souther.compiler.diag.Diagnostic;
import net.unit8.notation199x.pattern.PatternMeaning;
import souther.compiler.types.BindingId;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.CaseShape;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.TemporalRule;
import net.unit8.raoh.ErrorCodes;
import souther.runtime.BoundaryScalars;
import souther.temporal.TemporalForms;
import souther.compiler.types.Type;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.TypeSymbol;
import souther.compiler.check.TypeOps;
import souther.compiler.core.Core;

import souther.compiler.jvm.DecoderKind;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.types.TextRule;
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
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.HashMap;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;
import java.util.Optional;
import java.util.function.Consumer;

import static souther.compiler.codegen.Descriptors.*;
import static souther.compiler.codegen.JvmTypes.*;

/**
 * Generates a data/sum/unit type's decoders and encoders at the Raoh boundary (spec §codec-generation,
 * §case-propagation): the three input sources (neutral/JSON/jOOQ), object/leaf/newtype/sum decoding, a
 * newtype's invariant as Raoh constraints, the construct check, and the encoder raw expressions. Name
 * resolution and the synthetic-class sink come from {@link CodegenContext}; body expressions are emitted
 * through a {@link BodyGen} built per method.
 */
final class CodecGen {

    private final CodegenContext ctx;
    private final DerivedSymbols symbols;
    /** The $Dec class currently being generated — the owner of the {@code __rekey} helpers a
     * newtype-keyed map decoder references. Set per {@link #generateDecoderClass}. */
    private ClassDesc decoderClass;

    /** The decoder class whose body is being written, while one is: the owner of the {@code __text}
     *  a string leaf in it calls. Null outside {@link #buildDecoder}. */
    private ClassDesc textLeafOwner;

    /** Whether the decoder class being written reads a string, and so needs its {@code __text}. */
    private boolean usesTextLeaf;

    /** The temporals the decoder class being written reads from a bare value, and from text, each of
     *  which needs the helper that asks the language before Raoh parses. */
    private final Set<Type.Prim> bareTemporals = EnumSet.noneOf(Type.Prim.class);
    private final Set<Type.Prim> temporalTexts = EnumSet.noneOf(Type.Prim.class);

    /** The numbers the decoder class being written reads from a bare value, each of which needs its
     *  own helper, and whether it reads a {@code Decimal} from a JSON field. */
    private final Set<BareScalar> bareScalars = EnumSet.noneOf(BareScalar.class);
    private boolean usesJsonDecimalLeaf;

    /**
     * {@link Descriptors#build} of a class that is a decoder: one that reads a string carries the
     * {@code __text} its string leaf calls, and one that reads a temporal or an {@code Int} from a
     * bare value carries the helper for it, so a leaf is never emitted into a class that lacks what
     * it calls.
     */
    private byte[] buildDecoder(ClassDesc cdDec, Consumer<ClassBuilder> body) {
        textLeafOwner = cdDec;
        usesTextLeaf = false;
        bareScalars.clear();
        usesJsonDecimalLeaf = false;
        bareTemporals.clear();
        temporalTexts.clear();
        try {
            return build(cdDec, cb -> {
                body.accept(cb);
                if (usesTextLeaf) {
                    emitTextHelper(cb);
                }
                for (Type.Prim temporal : bareTemporals) {
                    emitBareTemporalHelper(cb, temporal);
                }
                for (Type.Prim temporal : temporalTexts) {
                    emitTemporalTextHelper(cb, temporal);
                }
                for (BareScalar scalar : bareScalars) {
                    emitBareScalarHelper(cb, scalar);
                }
                if (usesJsonDecimalLeaf) {
                    emitJsonDecimalHelper(cb);
                }
            });
        } finally {
            textLeafOwner = null;
        }
    }

    /** The value class the decoder being generated builds. Its {@code $Ctfe} carries the clause
     *  predicates a refined constraint reaches for, and asking for that class by the type it belongs
     *  to is what keeps the two from being named apart. Set beside {@link #decoderClass}. */
    private GeneratedClass.Value decodedValue;

    /** The patterns the decoder being generated holds a value to, and the constants their machines
     *  are loaded from ({@link #patternConstantsOf}). Set beside {@link #decoderClass}. */
    private Map<PatternMeaning, DynamicConstantDesc<Object>> patternConstants = Map.of();

    CodecGen(CodegenContext ctx) {
        this.ctx = ctx;
        this.symbols = ctx.symbols;
    }

    /** The three boundary input sources a decoder can read from (spec §external-representation, §codec-generation). */
    enum Src {
        NEUTRAL, JSON, JOOQ;

        /** Which of a type's decoders reads this source. What that decoder is called is the ABI's,
         *  and everything else this enum drives — the accessors, the leaf decoders, the object
         *  guard — is this package's. */
        DecoderKind kind() {
            return switch (this) {
                case NEUTRAL -> DecoderKind.VALUE;
                case JSON -> DecoderKind.JSON;
                case JOOQ -> DecoderKind.RECORD;
            };
        }
    }

    private ClassDesc cd(GeneratedClass generated) { return ctx.cd(generated); }
    private GeneratedClass.Value valueOf(Hir.Def def) { return new GeneratedClass.Value(def.declares()); }
    private GeneratedClass decoderOf(Hir.Def def, Src src) { return new GeneratedClass.Decoder(valueOf(def), src.kind()); }
    private ClassDesc cd(Hir.Def def) { return ctx.cd(def); }
    private ClassDesc cd(TypeSymbol typeName) { return ctx.cd(typeName); }
    private SequencedMap<String, Type> fieldTypes(Hir.Data data) { return ctx.laidOutFields(data); }
    private void unbox(CodeBuilder code, Type type, int slot) { JvmTypes.unbox(code, type, slot, ctx); }

    private static String srcFactory(Src s) {
        return switch (s) { case NEUTRAL -> "decoder"; case JSON -> "jsonDecoder"; case JOOQ -> "recordDecoder"; };
    }

    private static ClassDesc srcFieldOwner(Src s) {
        return switch (s) {
            case NEUTRAL -> CD_MapDecoders;
            case JSON -> CD_JsonDecoders;
            case JOOQ -> CD_JooqDecoders;
        };
    }

    private static MethodTypeDesc srcFieldMtd(Src s) { return s == Src.JOOQ ? MTD_fieldJooq : MTD_field; }

    private static MethodTypeDesc srcNullableFieldMtd(Src s) { return s == Src.JOOQ ? MTD_nullableFieldJooq : MTD_nullableField; }

    /** Leaf value decoders: JSON reads a JsonNode, the map/jOOQ column value is an Object. */
    private static ClassDesc srcLeafOwner(Src s) { return s == Src.JSON ? CD_JsonDecoders : CD_ObjectDecoders; }

    /** list()/map() combinator owner (JSON has its own; map/jOOQ leaf values are Objects). */
    private static ClassDesc srcListOwner(Src s) { return s == Src.JSON ? CD_JsonDecoders : CD_ObjectDecoders; }

    /** The {@code invokedynamic} call site that produces a {@code Function} wrapping
     *  {@code Sets::fromList} (a {@code List -> Set} dedup), for {@code Decoder.map} in a Set decoder. */
    private static DynamicCallSiteDesc setFromListCallSite() {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, CD_Sets, "fromList",
                MethodTypeDesc.of(CD_Set, CD_List));
        return Lambdas.callSite(Lambdas.Sam.FUNCTION, impl, MethodTypeDesc.of(CD_Set, CD_List));
    }

    /**
     * The only way this backend builds a decoder for text: Raoh's string leaf, admitted.
     *
     * <p>Every string that reaches the domain from outside comes through here — a field, a newtype's
     * base, a map's key, a list or set element, a sum's discriminator, an enumeration's name, a
     * temporal before it is parsed. It is one method rather than a step remembered at each of them
     * because "text that arrives is text, and canonical" is a property of the boundary and not of
     * any one shape, and the first attempt at it — normalizing where each caller happened to build a
     * leaf — left four paths behind, each found separately and after the fact.
     *
     * <p>{@code Strings::admission} is lifted through {@code Decoder.map}: it answers the NFC form,
     * or says why the text is not a {@code String} — it holds half of a surrogate pair, or its
     * canonical value is longer than a {@code String} holds. The class's own {@code __text} says that
     * as a {@code Result} through {@code flatMapWithPath}: each refusal is reported at the leaf's path
     * ({@link TextRule}) rather than thrown, since a decoder reports what it could not read, and both
     * are Raoh's {@code invalid_format}, with a message apiece. The runtime stops at the admission and
     * does not know Raoh, and two steps are what a leaf costs every text that arrives, so it is not a
     * refinement for each refusal. Not
     * {@code StringDecoder.normalize()}, which is Raoh's call into {@code java.text.Normalizer} and
     * answers for whatever Unicode version this JDK shipped with. {@code StringDecoder.from} wraps
     * the result back into a {@link CD_StringDecoder} so a constraint chained after this (a length
     * bound, {@code refine}) still resolves against one.
     *
     * <p>{@code ADecoderCanonicalizesEveryShapeTest} is the check that goes with it: it walks the
     * decoder shapes rather than this file, so a path added later that does not come through here
     * fails on what a caller would see rather than on how the code is written.
     */
    private void emitStringLeaf(CodeBuilder code, ClassDesc leafOwner) {
        if (textLeafOwner == null) {
            throw new IllegalStateException("a string leaf is emitted into a class that is not"
                    + " written by buildDecoder, so it has no __text to call");
        }
        code.invokestatic(leafOwner, "string", MTD_leafString);
        code.invokedynamic(STRINGS_ADMISSION);
        code.invokeinterface(CD_RDecoder, "map", MTD_Rdecoder_map);
        code.invokedynamic(textCallSite());
        code.invokeinterface(CD_RDecoder, "flatMapWithPath", MTD_flatMapWithPath);
        code.invokestatic(CD_StringDecoder, "from", MTD_stringDecoderFrom);
        usesTextLeaf = true;
    }

    /** {@code Strings::admission} as a {@code Function}, for the string leaf above. */
    private static final DynamicCallSiteDesc STRINGS_ADMISSION = Lambdas.callSite(
            Lambdas.Sam.FUNCTION,
            MethodHandleDesc.ofMethod(DirectMethodHandleDesc.Kind.STATIC, CD_Strings,
                    "admission", MTD_admission),
            MTD_admission);

    /** This class's {@code __text} as a {@code BiFunction}, for the string leaf above. */
    private DynamicCallSiteDesc textCallSite() {
        return Lambdas.callSite(Lambdas.Sam.BI_FUNCTION,
                MethodHandleDesc.ofMethod(DirectMethodHandleDesc.Kind.STATIC, textLeafOwner,
                        "__text", MTD_textOfAdmission),
                MTD_textOfAdmission);
    }

    /**
     * {@code static Result __text(TextAdmission admission, Path path)}: the text an admission let in,
     * or the failure at {@code path} saying why it is not a {@code String}.
     *
     * <p>Raoh's code {@code invalid_format} for either refusal, the one a temporal's text is refused
     * with too, and a message of its own for each ({@link TextRule}). Emitted into the class that
     * reads a string, as the other failures a decoder reports are, so that the runtime, which does
     * not know Raoh, stops at the admission.
     */
    private void emitTextHelper(ClassBuilder cb) {
        cb.withMethodBody("__text", MTD_textOfAdmission,
                ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC, code -> {
            Label notAdmitted = code.newLabel();
            Label notHalfAPair = code.newLabel();
            code.aload(0);
            code.instanceOf(CD_TextAdmitted);
            code.ifeq(notAdmitted);
            code.aload(0);
            code.checkcast(CD_TextAdmitted);
            code.invokevirtual(CD_TextAdmitted, "text", MTD_admittedText);
            code.invokestatic(CD_RResult, "ok", MTD_Rok, true);
            code.areturn();
            code.labelBinding(notAdmitted);
            code.aload(0);
            code.instanceOf(CD_TextNotText);
            code.ifeq(notHalfAPair);
            emitTextRefusal(code, TextRule.HALF_A_PAIR);
            code.labelBinding(notHalfAPair);
            emitTextRefusal(code, TextRule.NO_PLACE);
        });
    }

    private void emitTextRefusal(CodeBuilder code, String message) {
        code.aload(1);                                            // path
        code.loadConstant(TextRule.REFUSED);
        code.loadConstant(message);
        code.invokestatic(CD_Map, "of", MTD_mapOfNone, true);
        code.invokestatic(CD_RResult, "failCustom", MTD_Rfail4, true);
        code.areturn();
    }


    /**
     * Pushes the decoder a map key is read with. A key always arrives as a {@code String} — a JSON
     * object's keys are strings, and the neutral map's are too — so the temporal key is the
     * string-then-parse form for every source, not the direct temporal factory a field value uses.
     */
    private void emitKeyDecoder(CodeBuilder code, MapKeyRepresentation key) {
        switch (key) {
            // a named key runs its own decoder: a newtype's applies its invariant, an enumeration's
            // reads the case name
            case MapKeyRepresentation.NamedKey n -> invokeCodec(code, n.name(), "decoder", MTD_Rdecoder);
            // text is the string leaf itself, which canonicalizes and does nothing else; a temporal
            // is that leaf parsed
            case MapKeyRepresentation.Text _ -> emitStringLeaf(code, CD_ObjectDecoders);
            // Through the same builder a field's leaf goes through, so the language's question of
            // the text and the hold to the second are one rule at a field and under a key.
            case MapKeyRepresentation.Lexical l ->
                    emitTemporalFromText(code, CD_ObjectDecoders, l.leaf().type());
        }
    }

    /**
     * Whether a map's keys are remapped after decoding. Every boundary map's are.
     *
     * <p>A plain {@code String} key used to be left alone — it is already what the decoded object
     * carries — and that was true until text arriving from outside became canonical (ADR-0096). The
     * keys of a decoded map do not pass the string leaf that canonicalizes, so leaving them alone
     * left {@code Map<String, V>} the one place a boundary handed the domain text it had not
     * canonicalized: {@code Map.get} with a literal would miss a key written the other way, while
     * {@code Map<UserId, V>} beside it was canonical because a newtype key runs its own decoder here.
     *
     * <p>Kept as a question rather than deleted because the walk it turns on is also where a
     * canonicalization collision is caught, and that is a property of every key type, not of the
     * ones that need converting.
     */
    @SuppressWarnings("UnusedVariable")   // the key is what a narrowing would read; see above
    private static boolean needsRekey(MapKeyRepresentation key) {
        return true;
    }

    /** The name of the generated per-$Dec helper that remaps a decoded {@code Map<String, V>}'s keys
     *  into the key type, invariant-checked. A primitive key is named with a second {@code $} so it
     *  cannot collide with a data whose name is {@code Date}. */
    private static String rekeyMethod(MapKeyRepresentation key) {
        return switch (key) {
            case MapKeyRepresentation.NamedKey n -> "__rekey$"
                    + SoutherJvmAbi.nameOf(new GeneratedClass.Value(n.name())).binaryName().replace('.', '$');
            case MapKeyRepresentation.Lexical l -> "__rekey$$" + l.leaf();
        };
    }

    /** {@code invokedynamic} producing a {@code BiFunction<Map, Path, Result>} over the current $Dec
     *  class's {@code __rekey$<keyType>}, for {@code Decoder.flatMapWithPath} in a newtype-keyed map. */
    private static DynamicCallSiteDesc rekeyCallSite(ClassDesc cdDec, MapKeyRepresentation key) {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, cdDec, rekeyMethod(key), MTD_rekey);
        return Lambdas.callSite(Lambdas.Sam.BI_FUNCTION, impl, MTD_rekey);
    }

    /**
     * Pushes a {@code Function<K, String>} rendering a key as the text it crosses as, for
     * {@code Maps.mapKeys} before the String-keyed map encoder runs.
     *
     * <p>It is the key type's own encoder in both arms — a leaf factory for a primitive, the derived
     * {@code encoder()} for a named key — so what a name wraps is never read here. That is what
     * keeps this call site out of the admissible set: a newtype over a base admitted later writes
     * itself through the same two instructions, with nothing to add.
     *
     * <p>The same two {@code Runner.encodeKey} takes, reflectively. Both go through an encoder rather
     * than through an accessor, so neither can spell a key the other would not.
     */
    private void pushKeyRenderer(CodeBuilder code, MapKeyRepresentation key) {
        switch (key) {
            case MapKeyRepresentation.NamedKey n -> invokeCodec(code, n.name(), "encoder", MTD_Rencoder);
            case MapKeyRepresentation.Lexical l ->
                    code.invokestatic(CD_ObjectEncoders, leafEncoderName(l.leaf()), MTD_Rencode_leaf);
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
            cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withInterfaceSymbols(CD_REncoder);
            emitDefaultCtor(cb);
            emitSharedInstance(cb, cdEnc);
            // Dispatch on the runtime case type, encode that case as it writes itself, then add what
            // membership in this sum requires of it (spec §encoder-derivation).
            cb.withMethodBody("encode", MTD_Rencode, ClassFile.ACC_PUBLIC, code -> {
                for (Boundary.WireCase v : alternatives.wireCases()) {
                    TypeSymbol caseName = v.atom();
                    code.aload(1);
                    code.instanceOf(cd(caseName));
                    Label next = code.newLabel();
                    code.ifeq(next);
                    emitTagged(code, TypeOps.caseShape(caseName, symbols), form, v.tag(), () -> {
                        invokeCodec(code, caseName, "encoder", MTD_Rencoder);
                        code.aload(1);
                        code.invokeinterface(CD_REncoder, "encode", MTD_Rencode);
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

    byte[] generateSumDecoder(Hir.SumData sum, Boundary.Alternatives alternatives, Src src) {
        Boundary.Representation.Discriminated form = discriminated(alternatives);
        List<Boundary.WireCase> wireCases = alternatives.wireCases();
        ClassDesc cdDec = cd(decoderOf(sum, src));
        return buildDecoder(cdDec, cb -> {
            cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withInterfaceSymbols(CD_RDecoder);
            emitDefaultCtor(cb);
            emitSharedInstance(cb, cdDec);
            // Build a Raoh discriminate decoder and delegate: the tag is read from the
            // discriminator key of the source, each case dispatches to that case's decoder for the
            // same source (spec §sum-discrimination). discriminate/variant are the core (input-generic) combinators.
            cb.withMethodBody("decode", MTD_Rdecode, ClassFile.ACC_PUBLIC, code -> {
                // this=0, in=1, path=2, so 3 is the first free slot for the guard to hold the node in.
                emitObjectGuard(code, src, 3);
                code.loadConstant(form.tagKey());
                code.loadConstant(form.tagKey());
                emitStringLeaf(code, srcLeafOwner(src));
                code.invokestatic(srcFieldOwner(src), "field", srcFieldMtd(src));
                // `field` answers a CombinePart, and `discriminate` takes a Decoder — the conversion
                // is written rather than implicit, which is what keeps a part's field declaration
                // from being erased by a wrapper.
                code.invokeinterface(CD_CombinePart, "asDecoder", MTD_asDecoder);
                pushInt(code, wireCases.size());
                code.anewarray(CD_RVariant);
                int i = 0;
                for (Boundary.WireCase v : wireCases) {
                    code.dup();
                    pushInt(code, i);
                    code.loadConstant(v.tag());
                    // The mirror of what the encoder wrote: a case that wears the envelope is handed
                    // what is under the contents key and reads it as the standalone value it is,
                    // while a product and a unit read the discriminated object they are part of. So a
                    // wrapped case is read from under a key, which is not always this source's own
                    // decoder.
                    if (TypeOps.caseShape(v.atom(), symbols) == CaseShape.WRAPPED) {
                        code.loadConstant(form.contentsKey());
                        emitUnderAKeyDecoder(code, v.atom(), src);
                        code.invokestatic(srcFieldOwner(src), "field", srcFieldMtd(src));
                        code.invokeinterface(CD_CombinePart, "asDecoder", MTD_asDecoder);
                    } else {
                        invokeCodec(code, v.atom(), srcFactory(src), MTD_Rdecoder);
                    }
                    code.invokestatic(CD_RDecoders, "variant", MTD_Rvariant);
                    code.aastore();
                    i++;
                }
                code.invokestatic(CD_RDecoders, "discriminate", MTD_Rdiscriminate);
                code.aload(1);
                code.aload(2);
                code.invokeinterface(CD_RDecoder, "decode", MTD_Rdecode);
                code.areturn();
            });
        });
    }

    /**
     * Decodes a sum all of whose cases are unit data: the value is its case's name, so it reads a
     * bare string and answers that case's singleton (issue #161).
     *
     * <p>Which names are allowed is held by Raoh's {@code oneOf} over strings, because that
     * constraint states the rule a name is held to — one of these, compared exactly, case and all —
     * so a name no case answers to fails at the value's path as {@code oneOf} reports it (spec
     * §sum-discrimination). What is the enumeration's own is which case each allowed name is.
     */
    byte[] generateEnumSumDecoder(Hir.SumData sum, Boundary.Alternatives alternatives, Src src) {
        ClassDesc cdDec = cd(decoderOf(sum, src));
        List<Boundary.WireCase> cases = alternatives.wireCases();
        return buildDecoder(cdDec, cb -> {
            cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withInterfaceSymbols(CD_RDecoder);
            emitDefaultCtor(cb);
            emitSharedInstance(cb, cdDec);
            // The reader is a constant of the class, built once when it is first used: `oneOf`
            // sorts the names and words its message when it is made, which a decode is not to
            // pay for every time.
            cb.withMethodBody(READER, MTD_reader, ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC,
                    code -> {
                emitStringLeaf(code, srcLeafOwner(src));
                code.loadConstant(cases.size());
                code.anewarray(CD_String);
                for (int i = 0; i < cases.size(); i++) {
                    code.dup();
                    code.loadConstant(i);
                    code.loadConstant(cases.get(i).tag());
                    code.aastore();
                }
                code.invokevirtual(CD_StringDecoder, "oneOf", MTD_stringOneOf);
                code.invokedynamic(fromNameCallSite(cdDec));
                code.invokeinterface(CD_RDecoder, "flatMapWithPath", MTD_flatMapWithPath);
                code.areturn();
            });
            cb.withMethodBody("decode", MTD_Rdecode, ClassFile.ACC_PUBLIC, code -> {
                code.ldc(DynamicConstantDesc.ofNamed(ConstantDescs.BSM_INVOKE, "reader",
                        CD_RDecoder, MethodHandleDesc.ofMethod(DirectMethodHandleDesc.Kind.STATIC,
                                cdDec, READER, MTD_reader)));
                code.aload(1);
                code.aload(2);
                code.invokeinterface(CD_RDecoder, "decode", MTD_Rdecode);
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
     * than answering a failure the language never states.
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
                code.invokestatic(CD_RResult, "ok", MTD_Rok, true);
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
    private static final MethodTypeDesc MTD_reader = MethodTypeDesc.of(CD_RDecoder);

    private static DynamicCallSiteDesc fromNameCallSite(ClassDesc cdDec) {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, cdDec, "__fromName", MTD_fromName);
        return Lambdas.callSite(Lambdas.Sam.BI_FUNCTION, impl, MTD_fromName);
    }

    /** Encodes an enumeration to its case's name — the same string its decoder reads. */
    byte[] generateEnumSumEncoder(Hir.SumData sum) {
        ClassDesc cdEnc = cd(new GeneratedClass.Encoder(valueOf(sum)));
        return build(cdEnc, cb -> {
            cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withInterfaceSymbols(CD_REncoder);
            emitDefaultCtor(cb);
            emitSharedInstance(cb, cdEnc);
            cb.withMethodBody("encode", MTD_Rencode, ClassFile.ACC_PUBLIC, code -> {
                code.aload(1);
                code.invokestatic(cd(sum), TAG_METHOD, MTD_tag, true);
                code.areturn();
            });
        });
    }

    /** Decodes a unit: ignore the input (a unit carries no data) and build the singleton value. */
    byte[] generateUnitDecoder(ClassDesc cdU, ClassDesc cdDec) {
        return build(cdDec, cb -> {
            cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withInterfaceSymbols(CD_RDecoder);
            emitDefaultCtor(cb);
            emitSharedInstance(cb, cdDec);
            cb.withMethodBody("decode", MTD_Rdecode, ClassFile.ACC_PUBLIC, code -> {
                loadSharedInstance(code, cdU);   // a unit type has exactly one value
                code.invokestatic(CD_RResult, "ok", MTD_Rok, true);
                code.areturn();
            });
        });
    }

    /** Encodes a unit to an empty Map, the form spec §encoder-derivation gives a unit on its own; a
     *  sum encoder puts the discriminator tag in it, and an enumeration writes the case's name instead. */
    byte[] generateUnitEncoder(ClassDesc cdEnc) {
        return build(cdEnc, cb -> {
            cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withInterfaceSymbols(CD_REncoder);
            emitDefaultCtor(cb);
            emitSharedInstance(cb, cdEnc);
            cb.withMethodBody("encode", MTD_Rencode, ClassFile.ACC_PUBLIC, code -> {
                code.new_(CD_LinkedHashMap);
                code.dup();
                code.invokespecial(CD_LinkedHashMap, "<init>", MTD_void);
                code.areturn();
            });
        });
    }

    void emitFactory(ClassBuilder cb, String name, ClassDesc returnIface, Hir.Data data,
                             GeneratedClass codec) {
        ClassDesc impl = cd(codec);
        ClassDesc self = cd(data);
        MethodSignature sig = name.equals("decoder")
                ? decoderSig(self, isMapInput(data))
                : encoderSig(self, encoderOutput(data));
        emitCodecFactory(cb, name, returnIface, impl, sig);
    }

    /** Emits a static {@code decoder()}/{@code encoder()} factory returning a fresh {@code impl},
     * with a generic {@code Signature} so callers get {@code Decoder<..,T>} / {@code Encoder<T,..>}
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

    /** {@code Decoder<Map<String,Object>,T>} for objects/sums, {@code Decoder<Object,T>} for newtypes/units. */
    static MethodSignature decoderSig(ClassDesc type, boolean mapInput) {
        String in = mapInput
                ? "Ljava/util/Map<Ljava/lang/String;Ljava/lang/Object;>;"
                : "Ljava/lang/Object;";
        return MethodSignature.parseFrom(
                "()Lnet/unit8/raoh/decode/Decoder<" + in + type.descriptorString() + ">;");
    }

    /** {@code Encoder<T,O>}: {@code O} is {@code Map<String,Object>} for objects/sums/units, or the
     * bare (boxed) scalar for a newtype — a newtype encodes to a plain value, not a map. */
    static MethodSignature encoderSig(ClassDesc type, ClassDesc output) {
        String out = output.equals(CD_Map)
                ? "Ljava/util/Map<Ljava/lang/String;Ljava/lang/Object;>;"
                : output.descriptorString();
        return MethodSignature.parseFrom(
                "()Lnet/unit8/raoh/encode/Encoder<" + type.descriptorString() + out + ">;");
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

    /** Source-specific decoder factory signature: {@code Decoder<In,T>} with In per source. */
    static MethodSignature decoderSigFor(Src src, ClassDesc type, boolean mapInput) {
        String in = switch (src) {
            case NEUTRAL -> mapInput
                    ? "Ljava/util/Map<Ljava/lang/String;Ljava/lang/Object;>;"
                    : "Ljava/lang/Object;";
            case JSON -> "Ltools/jackson/databind/JsonNode;";
            case JOOQ -> "Lorg/jooq/Record;";
        };
        return MethodSignature.parseFrom(
                "()Lnet/unit8/raoh/decode/Decoder<" + in + type.descriptorString() + ">;");
    }

    /** Emits a source's decoder factory ({@code jsonDecoder()} / {@code recordDecoder()}). */
    void emitSourceFactory(ClassBuilder cb, Hir.Def def, Src src, boolean mapInput) {
        emitCodecFactory(cb, srcFactory(src), CD_RDecoder, cd(decoderOf(def, src)),
                decoderSigFor(src, cd(def), mapInput));
    }

    /** jOOQ rows are flat: a type is Record-decodable iff it is an object (or a sum of objects/units)
     * whose every field is a scalar column — a primitive, a newtype, or an optional of those; no
     * nested object, list, map, or sum. */
    boolean recordCompatible(Hir.Def def) {
        if (def instanceof Hir.SumData sum) {
            if (readsABareTag(sum)) {
                return false;   // an enumeration is a bare column, not a whole row (issue #161)
            }
            for (Hir.Name written : sum.cases()) {
                TypeSymbol caseName = Backend.names(written);
                Hir.Def caseDef = symbols.declaredNode(caseName);
                if (caseDef instanceof Hir.UnitData) continue;   // the discriminator alone, no column
                if (!(caseDef instanceof Hir.Data d)) return false;   // a nested sum is not a row
                // A case wearing the envelope reads the column the sum's decoder hands it, so it is a
                // row when what it wraps is a column.
                boolean ok = TypeOps.caseShape(caseName, symbols) == CaseShape.WRAPPED
                        ? flatColumn(TypeOps.newtypeInner(caseName, symbols))
                        : isFlatObject(d);
                if (!ok) return false;
            }
            return true;
        }
        return def instanceof Hir.Data data && isFlatObject(data);
    }

    private boolean isFlatObject(Hir.Data data) {
        if (!(symbols.derived(data).decoder() instanceof Hir.ObjectDecoder)) {
            return false;   // a newtype is a bare column, not a whole-row object
        }
        for (Type t : fieldTypes(data).values()) {
            if (!flatColumn(t)) return false;
        }
        return true;
    }

    private boolean flatColumn(Type t) {
        if (t instanceof Type.OptionOf o) return flatColumn(o.element());
        if (t instanceof Type.ListOf || t instanceof Type.MapOf || t instanceof Type.SetOf
                || t instanceof Type.Union) return false;
        if (t instanceof Type.Ref r) {
            return symbols.declarations().declaration(r.name()) instanceof Derived.Data d
                    && d.decoder() instanceof Hir.PrimDecoder;   // newtype column only
        }
        return true;   // primitive scalar
    }

    byte[] generateDecoderClass(ClassDesc cdName, Hir.Data data, Hir.DecoderDef dec,
                                        SequencedMap<String, Type> fields, Src src) {
        ClassDesc cdDec = cd(decoderOf(data, src));
        decoderClass = cdDec;
        decodedValue = valueOf(data);
        List<ValueShape.Invariant> invariants = invariantsOf(data);
        patternConstants = patternConstantsOf(invariants, data);
        return buildDecoder(cdDec, cb -> {
            cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withInterfaceSymbols(CD_RDecoder);
            emitDefaultCtor(cb);
            // Raoh Decoder SAM: decode(Object in, Path path) -> Result. this=0, in=1, path=2.
            cb.withMethodBody("decode", MTD_Rdecode, ClassFile.ACC_PUBLIC, code -> {
                AstExpressions gen = new AstExpressions(new BodyGen(ctx, code, data, cdName, 3));
                switch (dec) {
                    case Hir.PrimDecoder prim ->
                            emitPrimDecode(code, gen, prim, fields, src, invariants);
                    case Hir.ObjectDecoder obj -> emitObjectDecode(code, gen, obj, fields, src);
                    case Hir.NewtypeDecoder nt ->
                            emitNewtypeDecode(code, gen, nt, fields, src, invariants);
                }
            });
            // One key-remap helper per key type used as a map key anywhere in this decoder; the
            // decode body's flatMapWithPath call sites reference them.
            Map<String, MapKeyRepresentation> keyTypes = new LinkedHashMap<>();
            collectKeyedMapTypes(dec, keyTypes);
            for (MapKeyRepresentation key : keyTypes.values()) {
                emitRekeyHelper(cb, key);
            }
            emitSharedInstance(cb, cdDec);
            if (invariants.stream().anyMatch(c -> !c.projection().complete())) {
                emitInvariantFailureHelper(cb, data.name());
            }
            if (!patternConstants.isEmpty()) {
                emitPatternFailureHelper(cb);
            }
            if (constraintsOf(invariants).stream()
                    .anyMatch(BoundaryConstraint.OfMap.class::isInstance)) {
                RaohMapSizes.emitHelpers(cb);
            }
            if (constraintsOf(invariants).stream()
                    .anyMatch(BoundaryConstraint.Unique.class::isInstance)) {
                RaohListUnique.emitHelpers(cb);
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

    /** Collects the named types used as map keys anywhere in a derived decoder. */
    private void collectKeyedMapTypes(Hir.DecoderDef dec, Map<String, MapKeyRepresentation> out) {
        switch (dec) {
            case Hir.ObjectDecoder obj -> {
                for (Hir.Bind bind : obj.binds()) {
                    collectKeyedMapTypes(bind.ref(), out);
                }
            }
            case Hir.NewtypeDecoder nt -> collectKeyedMapTypes(nt.inner(), out);
            case Hir.PrimDecoder _ -> { }
        }
    }

    private void collectKeyedMapTypes(Hir.DecRef ref, Map<String, MapKeyRepresentation> out) {
        switch (ref) {
            case Hir.MapDecRef mp -> {
                if (needsRekey(mp.key())) {
                    out.putIfAbsent(rekeyMethod(mp.key()), mp.key());
                }
                collectKeyedMapTypes(mp.value(), out);
            }
            case Hir.ListDecRef l -> collectKeyedMapTypes(l.element(), out);
            case Hir.SetDecRef s -> collectKeyedMapTypes(s.element(), out);
            case Hir.OptionDecRef o -> collectKeyedMapTypes(o.element(), out);
            case Hir.PrimDecRef _ -> { }
            case Hir.DataDecRef _ -> { }
        }
    }

    /**
     * Emits {@code static Result __rekey$K(Map src, Path path)}: it remaps a decoded
     * {@code Map<String, V>}'s keys into the key type {@code K}, running {@code K}'s own decoder
     * (which applies K's invariant, and that of anything K wraps) on each key. Key issues accumulate
     * across the whole map (spec §case-propagation) and a failure lands at the key's path; on
     * success it returns a {@code Map<K, V>} in iteration order. Materialised as a {@code BiFunction} for {@code Decoder.flatMapWithPath}.
     */
    private void emitRekeyHelper(ClassBuilder cb, MapKeyRepresentation key) {
        cb.withMethodBody(rekeyMethod(key), MTD_rekey, ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC,
                code -> {
            // locals: src=0, path=1, keyDec=2, out=3, issues=4, it=5, entry=6, key=7, kr=8, decoded=9
            emitKeyDecoder(code, key);
            code.astore(2);                                              // keyDec = K.decoder()
            code.new_(CD_LinkedHashMap);
            code.dup();
            code.invokespecial(CD_LinkedHashMap, "<init>", MTD_void);
            code.astore(3);                                             // out = new LinkedHashMap()
            code.getstatic(CD_RIssues, "EMPTY", CD_RIssues);
            code.astore(4);                                            // issues = Issues.EMPTY
            code.aload(0);
            code.invokeinterface(CD_Map, "entrySet", MTD_entrySet);
            code.invokeinterface(CD_Set, "iterator", MTD_iterator);
            code.astore(5);                                            // it = src.entrySet().iterator()

            Label loop = code.newLabel();
            Label done = code.newLabel();
            code.labelBinding(loop);
            code.aload(5);
            code.invokeinterface(CD_Iterator, "hasNext", MTD_hasNext);
            code.ifeq(done);
            code.aload(5);
            code.invokeinterface(CD_Iterator, "next", MTD_getKeyValue);
            code.checkcast(CD_MapEntry);
            code.astore(6);                                            // entry = it.next()
            code.aload(6);
            code.invokeinterface(CD_MapEntry, "getKey", MTD_getKeyValue);
            code.astore(7);                                            // key = entry.getKey()
            // kr = keyDec.decode(key, path.append((String) key))
            code.aload(2);
            code.aload(7);
            code.aload(1);
            code.aload(7);
            code.checkcast(CD_String);
            code.invokevirtual(CD_RPath, "append", MTD_Path_append);
            code.invokeinterface(CD_RDecoder, "decode", MTD_Rdecode);
            code.astore(8);                                            // kr
            code.aload(8);
            code.instanceOf(CD_RErr);
            Label ok = code.newLabel();
            code.ifeq(ok);
            // Err: issues = issues.merge(((Err) kr).issues())
            code.aload(4);
            code.aload(8);
            code.checkcast(CD_RErr);
            code.invokevirtual(CD_RErr, "issues", MTD_Err_issues);
            code.invokevirtual(CD_RIssues, "merge", MTD_Issues_merge);
            code.astore(4);
            ctx.countOneStep(code);
            code.goto_(loop);
            code.labelBinding(ok);
            code.aload(8);
            code.checkcast(CD_ROk);
            code.invokevirtual(CD_ROk, "value", MTD_Object);
            code.astore(9);                                            // decoded = the remapped key
            // Two source keys can be one decoded key: canonicalizing (ADR-0096) makes text written
            // two ways into one text, and a newtype key's invariant can map two spellings together.
            // A Set may collapse them — equivalent text is one element — but a map would lose the
            // first key's value to the second with nothing said, so it is a failure at the key.
            code.aload(3);
            code.aload(9);
            code.invokeinterface(CD_Map, "containsKey", MTD_Map_containsKey);
            Label fresh = code.newLabel();
            code.ifeq(fresh);
            code.aload(4);
            code.aload(1);
            code.aload(7);
            code.checkcast(CD_String);
            code.invokevirtual(CD_RPath, "append", MTD_Path_append);
            code.loadConstant("duplicate_key");
            code.loadConstant("two keys are the same key once decoded");
            code.invokestatic(CD_RResult, "fail", MTD_Rfail, true);
            code.checkcast(CD_RErr);
            code.invokevirtual(CD_RErr, "issues", MTD_Err_issues);
            code.invokevirtual(CD_RIssues, "merge", MTD_Issues_merge);
            code.astore(4);
            ctx.countOneStep(code);
            code.goto_(loop);
            code.labelBinding(fresh);
            // out.put(decoded, entry.getValue())
            code.aload(3);
            code.aload(9);
            code.aload(6);
            code.invokeinterface(CD_MapEntry, "getValue", MTD_getKeyValue);
            code.invokeinterface(CD_Map, "put", MTD_Map_put);
            code.pop();
            ctx.countOneStep(code);
            code.goto_(loop);

            code.labelBinding(done);
            code.aload(4);
            code.invokevirtual(CD_RIssues, "isEmpty", MTD_Issues_isEmpty);
            Label fail = code.newLabel();
            code.ifeq(fail);
            code.aload(3);
            code.invokestatic(CD_RResult, "ok", MTD_Rok, true);       // Result.ok(out)
            code.areturn();
            code.labelBinding(fail);
            code.aload(4);
            code.invokestatic(CD_RResult, "err", MTD_Rerr, true);    // Result.err(issues)
            code.areturn();
        });
    }

    /**
     * True when the type's neutral decoder is handed a {@code Map} (object/sum), false when it is
     * handed whatever value arrives (newtype/unit/enumeration). Used to bridge nested field-value
     * decoders with {@code nested()}.
     *
     * <p>A newtype is handed any value, whatever it wraps. Its decoder passes the value to the
     * decoder of the type it wraps, read as from under a key, so the bridge to a {@code Map} is put
     * where the wrapped type is an object or a sum. The answer is the declaration's own, and no
     * reader of it opens what the newtype wraps — nor does it follow a chain of newtypes to its end.
     */
    boolean isMapInput(Hir.Def def) {
        return isMapInputOf(def);
    }

    boolean isMapInput(Hir.Name typeName) {
        return isMapInput(Backend.names(typeName));
    }

    boolean isMapInput(TypeSymbol type) {
        return isMapInputOf(symbols.declaredNode(type));
    }

    /**
     * Whether a value of {@code sum} crosses as a bare tag rather than as an object.
     *
     * <p>Asked of {@link Boundary} and not worked out from the cases here. These two readers are
     * codecs asking what shape arrives and what shape a row is, which is the same question the sum's
     * own decoder and encoder are generated from — answered in a second place, it is a second answer
     * whatever it says today.
     */
    private boolean readsABareTag(Hir.SumData sum) {
        return Boundary.of(Type.ref(sum.declares()), ctx.kinds, ctx.sums)
                .representation() instanceof Boundary.Representation.Enumeration;
    }

    private boolean isMapInputOf(Hir.Def def) {
        if (def instanceof Hir.SumData sum) {
            // an enumeration arrives as its case's name, a bare string (issue #161)
            return !readsABareTag(sum);
        }
        return def instanceof Hir.Data data
                && symbols.derived(data).decoder() instanceof Hir.ObjectDecoder;
    }

    /** Pushes a Raoh leaf {@code Decoder} for a primitive value from the given source. */
    private void emitLeafDecoder(CodeBuilder code, LeafScalar kind, Src src) {
        ClassDesc owner = srcLeafOwner(src);
        switch (kind) {
            // A string that came from outside is let in — refused where it holds half of a
            // surrogate pair, canonicalized to NFC otherwise — before anything reads it.
            // Canonically equivalent forms are the same text by Unicode's own definition, and
            // Souther compares strings by their code points, so without this the same name typed on
            // two machines is two values: two Map keys, two Set members, and `==` false. It sits at
            // the leaf so every constraint chained after it — a length bound, a pattern — sees the
            // canonical form rather than whatever the sender's keyboard produced.
            case STRING -> {
                emitStringLeaf(code, owner);
            }
            case INT -> emitNumberLeaf(code, owner, BareScalar.INT);
            case BOOL -> code.invokestatic(owner, "bool", MTD_leafBool);
            case DECIMAL -> emitNumberLeaf(code, owner, BareScalar.DECIMAL);
            case DATE -> emitTemporalLeaf(code, src, Type.Prim.DATE);
            case TIME -> emitTemporalLeaf(code, src, Type.Prim.TIME);
            case DATETIME -> emitTemporalLeaf(code, src, Type.Prim.DATETIME);
            case INSTANT -> emitTemporalLeaf(code, src, Type.Prim.INSTANT);
        }
    }

    /** {@code Temporals::toTheSecond} as a {@code Predicate}, for the leaf refinement below. */
    private static final DynamicCallSiteDesc TO_THE_SECOND = Lambdas.callSite(
            Lambdas.Sam.PREDICATE,
            MethodHandleDesc.ofMethod(DirectMethodHandleDesc.Kind.STATIC, CD_Temporals,
                    "toTheSecond", MethodTypeDesc.of(ConstantDescs.CD_boolean, CD_Object)),
            MethodTypeDesc.of(ConstantDescs.CD_boolean, CD_Object));

    /**
     * Emits a temporal leaf decoder from text: Raoh's string leaf, asked whether the text is one,
     * parsed to build the value, and held to the second.
     *
     * <p>A {@code Time} and a {@code DateTime} are held to the second. They carry no fraction of one
     * (spec §a-local-temporal-is-held-to-the-second), so text that has one says something the domain
     * cannot hold, and the boundary reports that rather than dropping it: a value silently rounded
     * reads to everything downstream as the value that was sent.
     *
     * <p>Which text is a temporal is the language's and not the parser's (spec §temporal-text), so
     * the text is put to it by the class's own {@code __dateText} and its siblings before Raoh's
     * parse sees it, and the parse only builds the value. That also has to happen <em>before</em> the
     * parse for an {@code Instant}'s leap second: the JDK takes {@code 23:59:60} and answers
     * {@code 23:59:59}, so afterwards the two are one value and the substitution is invisible. An
     * offset is not refused here: it is the same moment spelled differently, and only the written
     * form is held to UTC (spec §temporal-literal, §a-leap-second-is-no-moment).
     */
    private void emitTemporalFromText(CodeBuilder code, ClassDesc leafOwner, Type.Prim temporal) {
        emitStringLeaf(code, leafOwner);
        code.invokedynamic(Lambdas.callSite(Lambdas.Sam.BI_FUNCTION,
                MethodHandleDesc.ofMethod(DirectMethodHandleDesc.Kind.STATIC, temporalHelperOwner(),
                        temporalTextHelper(temporal), MTD_Rdecode),
                MTD_temporalText));
        code.invokeinterface(CD_RDecoder, "flatMapWithPath", MTD_flatMapWithPath);
        code.invokestatic(CD_StringDecoder, "from", MTD_stringDecoderFrom);
        code.invokevirtual(CD_StringDecoder, rawFactory(temporal), MTD_leafTemporal);
        temporalTexts.add(temporal);
        emitToTheSecond(code, temporal);
    }

    /** The decoder class being written, which owns the helpers a temporal leaf calls. */
    private ClassDesc temporalHelperOwner() {
        if (textLeafOwner == null) {
            throw new IllegalStateException("a temporal leaf is emitted into a class that is not"
                    + " written by buildDecoder, so it has no helper to call");
        }
        return textLeafOwner;
    }

    /** Raoh's leaf that builds a temporal, once the text has been admitted. */
    private static String rawFactory(Type.Prim temporal) {
        return switch (temporal) {
            case DATE -> "date";
            case TIME -> "time";
            case DATETIME -> "dateTime";
            case INSTANT -> "iso8601";
            case INT, STRING, BOOL, DECIMAL, RATIONAL ->
                    throw new IllegalStateException(temporal + " is not a temporal");
        };
    }

    /** Holds a {@code Time} and a {@code DateTime} to the second, after the parse that produced one. */
    private void emitToTheSecond(CodeBuilder code, Type.Prim temporal) {
        if (!TemporalRule.of(temporal).guardsValue()) {
            return;
        }
        code.invokedynamic(TO_THE_SECOND);
        code.loadConstant(TemporalRule.REFUSED);
        code.loadConstant(TemporalRule.SUB_SECOND);
        code.invokevirtual(CD_TemporalDecoder, "refine", MTD_refineTemporal);
    }

    /** Emits a temporal leaf decoder at a field. {@code JsonDecoders} has no {@code date()} factory —
     * a JSON temporal is a string that is then parsed — whereas the neutral/jOOQ source has a direct
     * static one, which takes the value as itself where the caller hands over a real temporal.
     *
     * <p>Both put the text to {@link TemporalForms} before it is parsed, so a rule about what a
     * {@code Time} holds cannot be one thing at a field and another at a map key. Raoh's bare-value
     * factory parses a {@code String} inside itself, so a decoder that stands in front of it
     * (the class's own {@code __date} and its siblings) asks first, and a real temporal a Java
     * caller hands over goes through to Raoh as it was. */
    private void emitTemporalLeaf(CodeBuilder code, Src src, Type.Prim temporal) {
        if (src == Src.JSON) {
            emitTemporalFromText(code, CD_JsonDecoders, temporal);
            return;
        }
        code.new_(CD_TemporalDecoder);
        code.dup();
        code.invokedynamic(Lambdas.callSite(Lambdas.Sam.DECODER,
                MethodHandleDesc.ofMethod(DirectMethodHandleDesc.Kind.STATIC, temporalHelperOwner(),
                        bareTemporalHelper(temporal), MTD_Rdecode),
                MTD_Rdecode));
        code.invokespecial(CD_TemporalDecoder, "<init>", MTD_wrappingInit);
        bareTemporals.add(temporal);
        emitToTheSecond(code, temporal);
    }

    private static String bareTemporalHelper(Type.Prim temporal) {
        return "__" + rawFactory(temporal);
    }

    private static String temporalTextHelper(Type.Prim temporal) {
        return "__" + rawFactory(temporal) + "Text";
    }

    /**
     * {@code static Result __dateText(Object in, Path path)} and its siblings: the language's
     * question put to a text, as a step of a string decoder.
     *
     * <p>The runtime answers why a text is not the temporal, or null (spec §temporal-text), and a
     * refusal is said here as a failure at the path, in Raoh's {@code invalid_format} with the
     * reason's own wording. One question and one wording for every path a text arrives by, so what a
     * field, a key and a top-level argument refuse cannot come apart. Emitted into the class that
     * reads the temporal, as {@code __text} is, so that the runtime, which does not know Raoh, stops
     * at the fact.
     */
    private void emitTemporalTextHelper(ClassBuilder cb, Type.Prim temporal) {
        cb.withMethodBody(temporalTextHelper(temporal), MTD_Rdecode,
                ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC, code -> {
            Label admitted = emitTemporalRefusal(code, temporal);
            code.labelBinding(admitted);
            code.aload(0);
            code.invokestatic(CD_RResult, "ok", MTD_Rok, true);
            code.areturn();
        });
    }

    /**
     * {@code static Result __date(Object in, Path path)} and its siblings: what a bare-value temporal
     * leaf decodes with.
     *
     * <p>Raoh's {@code ObjectDecoders.date()} takes a real temporal as itself and parses a
     * {@code String} inside itself, so which text it takes would be whatever the Raoh it is built
     * against takes. The same question is asked first, and anything that is not a {@code String} is
     * not a text and goes to Raoh as it was, so the type check, the {@code required} answer and the
     * path stay Raoh's.
     */
    private void emitBareTemporalHelper(ClassBuilder cb, Type.Prim temporal) {
        cb.withMethodBody(bareTemporalHelper(temporal), MTD_Rdecode,
                ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC, code -> {
            Label admitted = emitTemporalRefusal(code, temporal);
            code.labelBinding(admitted);
            code.invokestatic(CD_ObjectDecoders, rawFactory(temporal), MTD_leafTemporal);
            code.aload(0);
            code.aload(1);
            code.invokeinterface(CD_RDecoder, "decode", MTD_Rdecode);
            code.areturn();
        });
    }

    /** Returns the failure at the path where the runtime says the value (argument 0) is not the
     *  temporal, and falls through to the label it answers where nothing is said. */
    private Label emitTemporalRefusal(CodeBuilder code, Type.Prim temporal) {
        return emitRefusal(code, CD_Temporals, bareRefusal(temporal), TemporalRule.REFUSED,
                Optional.empty());
    }

    /**
     * Returns the failure at the path (argument 1) where {@code owner.question} says the value
     * (argument 0) is not what is being read, and falls through to the label it answers where
     * nothing is said. The runtime answers the reason or null and does not know Raoh; a refusal is
     * a result here, worded as the reason words it.
     *
     * <p>Which of Raoh's codes it is says what kind of thing is wrong, and is the caller's:
     * {@code invalid_format} for a text whose shape is wrong, {@code type_mismatch} for a value of a
     * kind the position does not read. A mismatch carries {@code expected} and the carrier's class as
     * {@code actual}, as Raoh's own does, so a resolver that renders one renders this.
     */
    private Label emitRefusal(CodeBuilder code, ClassDesc owner, String question, String errorCode,
                              Optional<String> expected) {
        Label admitted = code.newLabel();
        code.aload(0);
        code.invokestatic(owner, question, MTD_temporalRefusal);
        code.astore(2);
        code.aload(2);
        code.ifnull(admitted);
        code.aload(1);                                            // path
        code.loadConstant(errorCode);
        code.aload(2);
        if (expected.isPresent()) {
            code.loadConstant("expected");
            code.loadConstant(expected.get());
            code.loadConstant("actual");
            code.aload(0);
            code.invokevirtual(ConstantDescs.CD_Object, "getClass", MTD_getClass);
            code.invokevirtual(CD_Class, "getSimpleName", MTD_getSimpleName);
            code.invokestatic(CD_Map, "of", MTD_mapOf2, true);
        } else {
            code.invokestatic(CD_Map, "of", MTD_mapOfNone, true);
        }
        code.invokestatic(CD_RResult, "failCustom", MTD_Rfail4, true);
        code.areturn();
        return admitted;
    }

    /**
     * The scalars whose bare-value reading is asked a question before Raoh reads them (spec
     * §a-boundary-scalar-is-read-not-converted): what Raoh takes is wider than the language reads,
     * and the difference is a value the decoder would make up.
     *
     * <p>An {@code Int} is read from an integer representation, and not from a {@code BigDecimal}
     * written with a scale because its value happens to be whole. A {@code Decimal} is read from an
     * exact number, and not from a {@code Double} or a {@code Float}, which may have been rounded
     * before they arrived and print the shortest text of the binary value they were rounded to. The
     * rest — the carriers Raoh takes, the range, the path — stays Raoh's.
     */
    private enum BareScalar {
        INT("__long", "intRefusal", "integer", "long_", CD_LongDecoder, MTD_leafLong),
        DECIMAL("__decimal", "decimalRefusal", "exact number", "decimal", CD_DecimalDecoder,
                MTD_leafDecimal);

        final String helper;
        final String question;
        final String expected;
        final String factory;
        final ClassDesc decoder;
        final MethodTypeDesc leaf;

        BareScalar(String helper, String question, String expected, String factory,
                   ClassDesc decoder, MethodTypeDesc leaf) {
            this.helper = helper;
            this.question = question;
            this.expected = expected;
            this.factory = factory;
            this.decoder = decoder;
            this.leaf = leaf;
        }
    }

    /**
     * An {@code Int} or a {@code Decimal} leaf. A bare value is asked first, by the class's own
     * {@code __long} or {@code __decimal}; a JSON field's {@code Int} needs no question, since
     * {@code JsonDecoders.long_()} takes an integer literal and no other, and its {@code Decimal} is
     * asked what kind of node it is ({@link #emitJsonDecimalHelper}).
     */
    private void emitNumberLeaf(CodeBuilder code, ClassDesc owner, BareScalar scalar) {
        if (owner.equals(CD_JsonDecoders) && scalar == BareScalar.INT) {
            code.invokestatic(owner, scalar.factory, scalar.leaf);
            return;
        }
        boolean json = owner.equals(CD_JsonDecoders);
        code.new_(scalar.decoder);
        code.dup();
        code.invokedynamic(Lambdas.callSite(Lambdas.Sam.DECODER,
                MethodHandleDesc.ofMethod(DirectMethodHandleDesc.Kind.STATIC, temporalHelperOwner(),
                        json ? JSON_DECIMAL_HELPER : scalar.helper, MTD_Rdecode),
                MTD_Rdecode));
        code.invokespecial(scalar.decoder, "<init>", MTD_wrappingInit);
        if (json) {
            usesJsonDecimalLeaf = true;
        } else {
            bareScalars.add(scalar);
        }
    }

    /** {@code static Result __long(Object in, Path path)} and {@code __decimal}: what a bare-value
     *  {@code Int} and {@code Decimal} decode with. */
    private void emitBareScalarHelper(ClassBuilder cb, BareScalar scalar) {
        cb.withMethodBody(scalar.helper, MTD_Rdecode,
                ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC, code -> {
            Label admitted = emitRefusal(code, CD_BoundaryScalars, scalar.question,
                    ErrorCodes.TYPE_MISMATCH,
                    Optional.of(scalar.expected));
            code.labelBinding(admitted);
            code.invokestatic(CD_ObjectDecoders, scalar.factory, scalar.leaf);
            code.aload(0);
            code.aload(1);
            code.invokeinterface(CD_RDecoder, "decode", MTD_Rdecode);
            code.areturn();
        });
    }

    private static final String JSON_DECIMAL_HELPER = "__decimalNode";

    /**
     * {@code static Result __decimalNode(Object in, Path path)}: what a JSON field's {@code Decimal}
     * decodes with.
     *
     * <p>The carrier a number node holds is asked the one question a bare {@code Double} or
     * {@code Float} is asked ({@link BoundaryScalars#decimalRefusal}): a fraction the reader has
     * parsed as a binary floating-point number is already the nearest {@code double}, and the
     * decimal that prints is a different number from the one written when that took more digits
     * than a {@code double} holds ({@code 0.10000000000000001} arrives as {@code 0.1}, which
     * nothing here can tell from a literal that said {@code 0.1}), while a fraction the reader kept
     * as a {@code BigDecimal} (Jackson's {@code USE_BIG_DECIMAL_FOR_FLOATS}) is read exactly. A
     * node that is not a number, and a {@code NaN} or an infinity, are Raoh's.
     */
    private void emitJsonDecimalHelper(ClassBuilder cb) {
        cb.withMethodBody(JSON_DECIMAL_HELPER, MTD_Rdecode,
                ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC, code -> {
            Label admitted = code.newLabel();
            code.aload(0);
            code.instanceOf(CD_JsonNode);
            code.ifeq(admitted);
            code.aload(0);
            code.checkcast(CD_JsonNode);
            code.invokevirtual(CD_JsonNode, "isNumber", MTD_nodeIs);
            code.ifeq(admitted);
            // The carrier a JSON number holds is asked the one question every reading of a bare
            // number asks (BoundaryScalars), so a double the reader parsed a fraction into is
            // refused here the same way a double at a bare value is.
            code.aload(0);
            code.checkcast(CD_JsonNode);
            code.invokevirtual(CD_JsonNode, "numberValue", MTD_nodeNumberValue);
            code.astore(2);
            code.aload(2);
            code.invokestatic(CD_BoundaryScalars, "decimalRefusal", MTD_temporalRefusal);
            code.astore(3);
            code.aload(3);
            code.ifnull(admitted);
            code.aload(1);                                        // path
            code.loadConstant(ErrorCodes.TYPE_MISMATCH);
            code.aload(3);
            code.loadConstant("expected");
            code.loadConstant(BareScalar.DECIMAL.expected);
            code.loadConstant("actual");
            code.aload(2);
            code.invokevirtual(ConstantDescs.CD_Object, "getClass", MTD_getClass);
            code.invokevirtual(CD_Class, "getSimpleName", MTD_getSimpleName);
            code.invokestatic(CD_Map, "of", MTD_mapOf2, true);
            code.invokestatic(CD_RResult, "failCustom", MTD_Rfail4, true);
            code.areturn();
            code.labelBinding(admitted);
            code.invokestatic(CD_JsonDecoders, "decimal", MTD_leafDecimal);
            code.aload(0);
            code.aload(1);
            code.invokeinterface(CD_RDecoder, "decode", MTD_Rdecode);
            code.areturn();
        });
    }

    /** The {@code Temporals} method that says why a text is not this temporal. */
    private static String bareRefusal(Type.Prim temporal) {
        return switch (temporal) {
            case DATE -> "dateRefusal";
            case TIME -> "timeRefusal";
            case DATETIME -> "dateTimeRefusal";
            case INSTANT -> "instantRefusal";
            case INT, STRING, BOOL, DECIMAL, RATIONAL ->
                    throw new IllegalStateException(temporal + " is not a temporal");
        };
    }

    private void emitPrimDecode(CodeBuilder code, AstExpressions gen, Hir.PrimDecoder prim,
                                SequencedMap<String, Type> fields, Src src,
                                List<ValueShape.Invariant> invariants) {
        Type inputType = TypeOps.primType(prim.from());
        ClassDesc leaf = srcLeafOwner(src);
        Carrier carrier = switch (prim.from()) {
            case TEXT -> Carrier.STRING;
            case INT -> Carrier.LONG;
            case DECIMAL -> Carrier.DECIMAL;
            case BOOL, DATE, TIME, DATETIME, INSTANT -> Carrier.PLAIN;
        };
        switch (prim.from()) {
            // Canonicalized before the constraints below read it, as a field's string is — a newtype
            // over Text is the other place text enters, and the two must agree or the same value
            // would be one length in a field and another on its own.
            case TEXT -> {
                emitStringLeaf(code, leaf);
            }
            case INT -> emitNumberLeaf(code, leaf, BareScalar.INT);
            case BOOL -> code.invokestatic(leaf, "bool", MTD_leafBool);
            case DECIMAL -> emitNumberLeaf(code, leaf, BareScalar.DECIMAL);
            case DATE -> emitTemporalLeaf(code, src, Type.Prim.DATE);
            case TIME -> emitTemporalLeaf(code, src, Type.Prim.TIME);
            case DATETIME -> emitTemporalLeaf(code, src, Type.Prim.DATETIME);
            case INSTANT -> emitTemporalLeaf(code, src, Type.Prim.INSTANT);
        }
        emitInvariantConstraints(code, inputType, carrier, invariants);
        code.aload(1);                                                 // in (bare value)
        code.aload(2);                                                 // path
        code.invokeinterface(CD_RDecoder, "decode", MTD_Rdecode);      // Result
        int rSlot = gen.slot(Type.STRING);
        code.astore(rSlot);
        code.aload(rSlot);
        code.instanceOf(CD_RErr);
        Label notErr = code.newLabel();
        code.ifeq(notErr);
        code.aload(rSlot);                                            // Err -> return as-is
        code.areturn();
        code.labelBinding(notErr);
        code.aload(rSlot);
        code.checkcast(CD_ROk);
        code.invokevirtual(CD_ROk, "value", MTD_Object);
        int inputSlot = gen.slot(inputType);
        unbox(code, inputType, inputSlot);
        gen.bind(prim.input().binding(), prim.input().name(), inputSlot, inputType);
        emitConstructCall(code, gen, prim.result(), fields);
    }

    /**
     * A newtype over a non-primitive Y: decode the whole input with Y's decoder, then wrap the
     * result in X (spec §newtype). Same Err short-circuit as {@link #emitPrimDecode}, but the leaf is
     * Y's decoder rather than a primitive one.
     */
    private void emitNewtypeDecode(CodeBuilder code, AstExpressions gen, Hir.NewtypeDecoder dec,
                                   SequencedMap<String, Type> fields, Src src,
                                   List<ValueShape.Invariant> invariants) {
        if (dec.inner() instanceof Hir.MapDecRef mp) {
            // The map's own decoder and its keys decoded, and then the clauses. What a clause is
            // about is the map the model declared — its keys converted and canonical — and every
            // clause is about that one value, so they run in the order they are declared on it. A
            // key that does not decode is no map of the model's yet, and is reported as that before
            // any clause is asked.
            emitDecoderObject(code, mp.value(), src);
            code.invokestatic(srcListOwner(src), "map", MTD_mapDec);
            code.invokedynamic(rekeyCallSite(decoderClass, mp.key()));
            code.invokeinterface(CD_RDecoder, "flatMapWithPath", MTD_flatMapWithPath);
            emitInvariantConstraints(code, bindType(dec.inner()), Carrier.MAP, invariants);
        } else {
            emitDecoderObject(code, dec.inner(), src);                // Y's decoder (for this source)
            // A list is decoded by Raoh's list decoder, whose constraints a clause can be stated
            // as. Anything else is a plain Decoder, on which a clause is checked as itself (and
            // again by __construct).
            Carrier carrier = dec.inner() instanceof Hir.ListDecRef ? Carrier.LIST : Carrier.PLAIN;
            emitInvariantConstraints(code, bindType(dec.inner()), carrier, invariants);
        }
        code.aload(1);                                               // in
        code.aload(2);                                               // path
        code.invokeinterface(CD_RDecoder, "decode", MTD_Rdecode);   // Result
        int rSlot = gen.slot(Type.STRING);
        code.astore(rSlot);
        code.aload(rSlot);
        code.instanceOf(CD_RErr);
        Label notErr = code.newLabel();
        code.ifeq(notErr);
        code.aload(rSlot);                                          // Err -> return as-is
        code.areturn();
        code.labelBinding(notErr);
        code.aload(rSlot);
        code.checkcast(CD_ROk);
        code.invokevirtual(CD_ROk, "value", MTD_Object);
        Type innerType = bindType(dec.inner());
        int inSlot = gen.slot(innerType);
        unbox(code, innerType, inSlot);                             // cast Object -> Y, store
        gen.bind(dec.input().binding(), dec.input().name(), inSlot, innerType);
        emitConstructCall(code, gen, dec.result(), fields);
    }

    /**
     * Emits the JSON decoder's shape check: the node this decoder was handed either holds an object
     * or it does not, and that is one fact about one node, reported at that node.
     *
     * <p>Without it the fields answer it one at a time. {@code JsonDecoders.field} reads its name out
     * of the node it is given and rejects a node that is not an object — at the field's own path, once
     * per field — so a node of the wrong shape becomes one report per declared field, each naming a
     * field the author wrote correctly, and a nested one lands on the record's first field instead of
     * the record. A data whose fields are all optional went the other way and decoded, since an absent
     * field is what {@code nullableField} makes of a node it cannot read.
     *
     * <p>A sum is read as an object too — its discriminator is a field — so it asks the same question
     * in the same place. Left to the discriminator, the mismatch is blamed on the discriminator key,
     * the one field of the object the author never writes.
     *
     * <p>Only the JSON source needs it. The neutral decoder is handed a {@code Map} by its own
     * signature, and a nested one is bridged through {@code MapDecoders.nested}, which asks the same
     * question at the same place; a jOOQ {@code Record} is a row and has no other shape to be.
     *
     * @param node a free local slot, which the guard holds the cast node in
     */
    private void emitObjectGuard(CodeBuilder code, Src src, int node) {
        if (src != Src.JSON) {
            return;
        }
        Label required = code.newLabel();
        Label ok = code.newLabel();
        code.aload(1);
        code.ifnull(required);
        code.aload(1);
        code.checkcast(CD_JsonNode);
        code.astore(node);
        code.aload(node);
        code.invokevirtual(CD_JsonNode, "isNull", MTD_nodePredicate);
        code.ifne(required);
        code.aload(node);
        code.invokevirtual(CD_JsonNode, "isMissingNode", MTD_nodePredicate);
        code.ifne(required);
        code.aload(node);
        code.invokevirtual(CD_JsonNode, "isObject", MTD_nodePredicate);
        code.ifne(ok);

        code.aload(2);                                            // path
        code.loadConstant("type_mismatch");
        code.loadConstant("expected object");
        code.loadConstant("expected");
        code.loadConstant("object");
        code.loadConstant("actual");
        code.aload(node);
        code.invokevirtual(CD_JsonNode, "getNodeType", MTD_getNodeType);
        code.invokevirtual(CD_JsonNodeType, "name", MTD_enumName);
        code.getstatic(CD_Locale, "ROOT", CD_Locale);
        code.invokevirtual(CD_String, "toLowerCase", MTD_toLowerCase);
        code.invokestatic(CD_Map, "of",
                MethodTypeDesc.of(CD_Map, CD_Object, CD_Object, CD_Object, CD_Object), true);
        code.invokestatic(CD_RResult, "fail", MTD_Rfail4, true);
        code.areturn();

        code.labelBinding(required);
        code.aload(2);
        code.loadConstant("required");
        code.loadConstant("is required");
        code.invokestatic(CD_RResult, "fail", MTD_Rfail, true);
        code.areturn();

        code.labelBinding(ok);
    }

    private void emitObjectDecode(CodeBuilder code, AstExpressions gen, Hir.ObjectDecoder obj,
                                  SequencedMap<String, Type> fields, Src src) {
        emitObjectGuard(code, src, gen.slot(Type.STRING));
        List<Hir.Bind> binds = obj.binds();
        int[] resultSlots = new int[binds.size()];
        for (int i = 0; i < binds.size(); i++) {
            Hir.Bind bind = binds.get(i);
            code.loadConstant(bind.key());
            if (bind.ref() instanceof Hir.OptionDecRef opt) {
                emitDecoderObject(code, opt.element(), src);
                code.invokestatic(srcFieldOwner(src), "nullableField", srcNullableFieldMtd(src));
            } else {
                emitDecoderObject(code, bind.ref(), src);
                code.invokestatic(srcFieldOwner(src), "field", srcFieldMtd(src));
            }
            code.aload(1);   // in (Map)
            code.aload(2);   // path
            // A part decodes on its own and appends its own name to the path, so a field read here
            // reports where it would inside a combine.
            code.invokeinterface(CD_CombinePart, "decode", MTD_partDecode);
            int rSlot = gen.slot(Type.STRING);
            code.astore(rSlot);
            resultSlots[i] = rSlot;
        }

        // Accumulate every field's issues (applicative), then fail once if any (spec §case-propagation).
        int accSlot = gen.slot(Type.STRING);
        code.getstatic(CD_RIssues, "EMPTY", CD_RIssues);
        code.astore(accSlot);
        for (int i = 0; i < binds.size(); i++) {
            code.aload(resultSlots[i]);
            code.instanceOf(CD_RErr);
            Label notErr = code.newLabel();
            code.ifeq(notErr);
            code.aload(accSlot);
            code.aload(resultSlots[i]);
            code.checkcast(CD_RErr);
            code.invokevirtual(CD_RErr, "issues", MTD_Err_issues);
            code.invokevirtual(CD_RIssues, "merge", MTD_Issues_merge);
            code.astore(accSlot);
            code.labelBinding(notErr);
        }
        code.aload(accSlot);
        code.invokevirtual(CD_RIssues, "isEmpty", MTD_Issues_isEmpty);
        Label ok = code.newLabel();
        code.ifne(ok);
        code.aload(accSlot);
        code.invokestatic(CD_RResult, "err", MTD_Rerr, true);
        code.areturn();
        code.labelBinding(ok);

        for (int i = 0; i < binds.size(); i++) {
            Hir.Bind bind = binds.get(i);
            Type t = bindType(bind.ref());
            code.aload(resultSlots[i]);
            code.checkcast(CD_ROk);
            code.invokevirtual(CD_ROk, "value", MTD_Object);
            if (bind.ref() instanceof Hir.OptionDecRef) {
                code.invokestatic(CD_Option, "ofNullable", MTD_ofNullable, true);
                int vSlot = gen.slot(t);
                code.astore(vSlot);
                gen.bind(bind.binder().binding(), bind.binder().name(), vSlot, t);
            } else {
                int vSlot = gen.slot(t);
                unbox(code, t, vSlot);
                gen.bind(bind.binder().binding(), bind.binder().name(), vSlot, t);
            }
        }
        emitConstructCall(code, gen, obj.result(), fields);
    }

    private Type bindType(Hir.DecRef ref) {
        return switch (ref) {
            case Hir.PrimDecRef p -> TypeOps.primType(p.kind());
            case Hir.DataDecRef d -> Type.ref(Backend.names(d.typeName()));
            case Hir.ListDecRef l -> Type.list(bindType(l.element()));
            case Hir.SetDecRef s -> Type.set(bindType(s.element()));
            case Hir.OptionDecRef o -> Type.option(bindType(o.element()));
            case Hir.MapDecRef mp -> Type.map(mp.key().type(), bindType(mp.value()));
        };
    }

    /**
     * The decoder for a named type read from under a key of {@code src} — a data's field, or the
     * envelope key a sum's wrapped case sits under.
     *
     * <p>Taking a value out from under a key leaves the source behind, and by how much depends on the
     * source. A jOOQ row is flat, so what is under a key is a column and not a row: only the type's
     * own {@code Object} decoder can read it, and a type that is not a whole row has no
     * {@code recordDecoder()} to reach for anyway. A neutral object's value is a bare {@code Object},
     * so a type that reads a {@code Map} is bridged to one — which is also where a value of the wrong
     * shape is told so at that key. A JSON object's value is a {@code JsonNode} like the object
     * holding it, so that source alone carries through.
     */
    private void emitUnderAKeyDecoder(CodeBuilder code, Hir.Name typeName, Src src) {
        emitUnderAKeyDecoder(code, Backend.names(typeName), src);
    }

    private void emitUnderAKeyDecoder(CodeBuilder code, TypeSymbol typeName, Src src) {
        switch (src) {
            case NEUTRAL -> {
                invokeCodec(code, typeName, "decoder", MTD_Rdecoder);
                if (isMapInput(typeName)) {
                    code.invokestatic(CD_MapDecoders, "nested", MTD_nested);   // Decoder<Map> -> Decoder<Object>
                }
            }
            case JSON -> invokeCodec(code, typeName, "jsonDecoder", MTD_Rdecoder);
            case JOOQ -> invokeCodec(code, typeName, "decoder", MTD_Rdecoder);
        }
    }

    /** Pushes a {@code Decoder} for the given field-value reference, for the given source. */
    private void emitDecoderObject(CodeBuilder code, Hir.DecRef ref, Src src) {
        switch (ref) {
            case Hir.PrimDecRef p -> emitLeafDecoder(code, p.kind(), src);
            case Hir.DataDecRef d -> emitUnderAKeyDecoder(code, d.typeName(), src);
            case Hir.ListDecRef l -> {
                emitDecoderObject(code, l.element(), src);
                code.invokestatic(srcListOwner(src), "list", MTD_listDec);
            }
            case Hir.SetDecRef s -> {
                emitDecoderObject(code, s.element(), src);
                code.invokestatic(srcListOwner(src), "list", MTD_listDec);   // Decoder<I, List<T>>
                code.invokedynamic(setFromListCallSite());                   // Function: List -> Set
                code.invokeinterface(CD_RDecoder, "map", MTD_Rdecoder_map);  // Decoder<I, Set<T>> (dedup)
            }
            // An optional standing where there is no key to be missing — a member, a map's value.
            // There null is the whole of what absence is (spec [#absence-is-written-as-null]), so
            // the element decoder is the present one made null-tolerant and lifted into an Option.
            // A field's optional never reaches here: its key is read by `nullableField` instead.
            case Hir.OptionDecRef o -> {
                emitDecoderObject(code, o.element(), src);
                code.invokestatic(srcListOwner(src), "nullable", MTD_nullableDec);
                code.invokedynamic(optionOfNullableCallSite());              // Function: Object -> Option
                code.invokeinterface(CD_RDecoder, "map", MTD_Rdecoder_map);  // Decoder<I, Option<T>>
            }
            case Hir.MapDecRef mp -> {
                emitDecoderObject(code, mp.value(), src);
                code.invokestatic(srcListOwner(src), "map", MTD_mapDec);   // Decoder<I, Map<String,V>>
                if (needsRekey(mp.key())) {
                    // Remap the String keys into the key type: a newtype's own decoder runs its
                    // invariant, a temporal's parses the ISO form.
                    code.invokedynamic(rekeyCallSite(decoderClass, mp.key()));   // BiFunction<Map,Path,Result>
                    code.invokeinterface(CD_RDecoder, "flatMapWithPath", MTD_flatMapWithPath);
                }
            }
        }
    }

    /**
     * The decoder a newtype's clauses are chained onto, which is what decides the methods a
     * constraint and a clause's own check are chained through.
     *
     * <p>A typed decoder keeps its type through its own {@code refine}, so a constraint can follow a
     * clause's check and the clauses go on in the order they are declared.
     */
    private enum Carrier {
        STRING(CD_StringDecoder),
        LONG(CD_LongDecoder),
        DECIMAL(CD_DecimalDecoder),
        LIST(CD_ListDecoder),
        /** The map the model declares, its keys decoded: a plain decoder, onto which a map's size
         *  constraints are lowered ({@link RaohMapSizes}). */
        MAP(null),
        /** Any other decoder, on which nothing but a clause's own check is chained. */
        PLAIN(null);

        /** The typed decoder's class, or null where the chain is on the plain {@code Decoder}. */
        final ClassDesc typed;

        Carrier(ClassDesc typed) {
            this.typed = typed;
        }
    }

    /**
     * Constrains the decoder on the stack with the newtype's invariant, clause by clause in the order
     * they are declared. What the checker found a clause to be as constraints
     * ({@link ConstraintProjection}) is chained as those constraints, so the failure carries the
     * constraint's code, metadata and default message at the value's path — {@code too_short} with
     * {@code min}, not one {@code invariant_violation} for every rule in the model. Where they are
     * not the whole clause, the clause's own check follows them, under the shared code with the rejecting type and, where the clause has one, its
     * name in the metadata. That failure is built here rather than through {@code refine}'s message
     * overload, which mints a custom-message issue a resolver refuses to touch — an invariant's text
     * must stay replaceable.
     *
     * <p>Raoh chains with {@code flatMap}, so the first failure stops the rest and the chain's order is
     * the order a failure is reported in — the same order {@code __construct} decides in, so the
     * boundary and an attempted construction name the same clause for the same value.
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
                // The clause is captured off the stack, so a clause with no name captures null —
                // a constant-pool entry could not have been one.
                if (clause.name().isPresent()) {
                    code.loadConstant(clause.name().get());
                } else {
                    code.aconst_null();
                }
                code.invokedynamic(invariantFailureCallSite());
                if (carrier.typed != null) {
                    code.invokevirtual(carrier.typed, "refine",
                            MethodTypeDesc.of(carrier.typed, CD_Predicate, CD_BiFunction));
                } else {
                    code.invokeinterface(CD_RDecoder, "refine", MTD_Rrefine);
                }
            }
        }
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
            case BoundaryConstraint.MinLength m -> {
                pushInt(code, m.n());
                code.invokevirtual(CD_StringDecoder, "minLength", MTD_strLengthBound);
            }
            case BoundaryConstraint.MaxLength m -> {
                pushInt(code, m.n());
                code.invokevirtual(CD_StringDecoder, "maxLength", MTD_strLengthBound);
            }
            case BoundaryConstraint.FixedLength f -> {
                pushInt(code, f.n());
                code.invokevirtual(CD_StringDecoder, "fixedLength", MTD_strLengthBound);
            }
            case BoundaryConstraint.Pattern p -> {
                // The machine is a constant of the class, built once when it is first loaded. What a
                // failure quotes is the pattern the call was given, built by `__patternFailure`.
                DynamicConstantDesc<Object> machine = patternConstants.get(p.meaning());
                if (machine == null) {
                    throw new IllegalStateException(
                            "a pattern the decoder class holds no constant for: " + p);
                }
                code.ldc(machine);
                code.loadConstant(p.written());
                code.invokedynamic(patternFailureCallSite());
                code.invokevirtual(CD_StringDecoder, "refine", MTD_refineStringFailing);
            }
            case BoundaryConstraint.Min m -> {
                code.loadConstant(m.n());
                code.invokevirtual(CD_LongDecoder, "min", MTD_longBound);
            }
            case BoundaryConstraint.Max m -> {
                code.loadConstant(m.n());
                code.invokevirtual(CD_LongDecoder, "max", MTD_longBound);
            }
            case BoundaryConstraint.Positive _ ->
                    code.invokevirtual(CD_LongDecoder, "positive", MTD_longSign);
            case BoundaryConstraint.NonNegative _ ->
                    code.invokevirtual(CD_LongDecoder, "nonNegative", MTD_longSign);
            case BoundaryConstraint.DecimalMin m -> {
                emitBigDecimal(code, m.n());
                code.invokevirtual(CD_DecimalDecoder, "min", MTD_decBound);
            }
            case BoundaryConstraint.DecimalMax m -> {
                emitBigDecimal(code, m.n());
                code.invokevirtual(CD_DecimalDecoder, "max", MTD_decBound);
            }
            case BoundaryConstraint.DecimalPositive _ ->
                    code.invokevirtual(CD_DecimalDecoder, "positive", MTD_decSign);
            case BoundaryConstraint.DecimalNonNegative _ ->
                    code.invokevirtual(CD_DecimalDecoder, "nonNegative", MTD_decSign);
            case BoundaryConstraint.NonEmpty _ ->
                    code.invokevirtual(CD_ListDecoder, "nonempty", MTD_listSign);
            case BoundaryConstraint.MinSize m -> {
                pushInt(code, m.n());
                code.invokevirtual(CD_ListDecoder, "minSize", MTD_listSizeBound);
            }
            case BoundaryConstraint.MaxSize m -> {
                pushInt(code, m.n());
                code.invokevirtual(CD_ListDecoder, "maxSize", MTD_listSizeBound);
            }
            case BoundaryConstraint.FixedSize f -> {
                pushInt(code, f.n());
                code.invokevirtual(CD_ListDecoder, "fixedSize", MTD_listSizeBound);
            }
            case BoundaryConstraint.Unique _ -> RaohListUnique.emit(code, decoderClass);
            case BoundaryConstraint.OfMap m -> RaohMapSizes.emit(code, decoderClass, m);
        }
    }

    private void emitBigDecimal(CodeBuilder code, java.math.BigDecimal value) {
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
     * {@code invokedynamic} producing the {@code BiFunction} that builds a refined clause's failure —
     * the issue this decoder reports when the value breaks a rule no constraint states. The clause's
     * name is captured, so one helper serves every refined clause; a clause declared without a name
     * captures null, which is what says there is nothing to tell it apart by.
     */
    private DynamicCallSiteDesc invariantFailureCallSite() {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, decoderClass, "__invariantFailure",
                MTD_invariantFailureNamed);
        return Lambdas.callSite(Lambdas.Sam.BI_FUNCTION, impl, MTD_invariantFailure,
                CD_String);                                                      // captures the clause
    }

    /**
     * {@code invokedynamic} producing the {@code BiFunction} that builds a pattern's failure, with
     * the pattern the call was given captured.
     */
    private DynamicCallSiteDesc patternFailureCallSite() {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, decoderClass, "__patternFailure",
                MTD_invariantFailureNamed);
        return Lambdas.callSite(Lambdas.Sam.BI_FUNCTION, impl, MTD_invariantFailure,
                CD_String);                                                      // captures the pattern
    }

    /**
     * {@code static Result __patternFailure(String written, Object value, Path path)}: the issue a
     * value that does not match its format reports.
     *
     * <p>What Raoh's own {@code pattern} constraint reports — the code and message key
     * {@code invalid_format} and a default message a {@code MessageResolver} may replace — with the
     * pattern in the metadata being the one the author's call was given rather than the one the
     * matcher runs. Which text a matcher runs is this backend's; which pattern a value was held to
     * is the model's, and is what a carrier other than the JVM reports too.
     */
    private void emitPatternFailureHelper(ClassBuilder cb) {
        cb.withMethodBody("__patternFailure", MTD_invariantFailureNamed,
                ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC, code -> {
            code.aload(2);                                            // path
            code.loadConstant("invalid_format");
            code.loadConstant("invalid format");
            code.loadConstant("pattern");
            code.aload(0);                                            // the pattern as written
            code.invokestatic(CD_Map, "of", MTD_mapOfOne, true);
            code.invokestatic(CD_RResult, "fail", MTD_Rfail4, true);
            code.areturn();
        });
    }

    /**
     * {@code static Result __invariantFailure(String clause, Object value, Path path)}: the issue a
     * refined clause reports. It is a {@code Result.fail}, so the message is a default one a
     * {@code MessageResolver} may replace; the rejecting type and the clause travel in the metadata,
     * which is what a resolver switches on when the code is the shared one.
     *
     * <p>Both come from {@link souther.runtime.InvariantFailure}, the same value {@code __construct}
     * hands its caller — so the boundary and an abort say the same thing about the same failure.
     */
    private void emitInvariantFailureHelper(ClassBuilder cb, String typeName) {
        cb.withMethodBody("__invariantFailure", MTD_invariantFailureNamed,
                ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC, code -> {
            code.new_(CD_InvariantFailure);
            code.dup();
            code.loadConstant(ctx.module());
            code.loadConstant(typeName);
            code.aload(0);                                            // the clause, or null
            code.invokespecial(CD_InvariantFailure, "<init>",
                    MethodTypeDesc.of(ConstantDescs.CD_void, CD_String, CD_String, CD_String));
            int failure = 3;
            code.astore(failure);
            code.aload(2);                                            // path
            code.loadConstant("invariant_violation");
            code.aload(failure);
            code.invokevirtual(CD_InvariantFailure, "toString", MethodTypeDesc.of(CD_String));
            code.aload(failure);
            code.invokevirtual(CD_InvariantFailure, "meta", MTD_failureMeta);
            code.invokestatic(CD_RResult, "fail", MTD_Rfail4, true);
            code.areturn();
        });
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
     * Emits the {@code __construct} call for a decoded value and maps an invariant failure to a Raoh
     * failure at the value's path. Must be emitted inside a {@code decode(Object, RPath)} body: it
     * reads the path from local slot 2 (the {@code RPath} parameter). Its three callers —
     * {@code emitPrimDecode}, {@code emitNewtypeDecode}, {@code emitObjectDecode} — are all such
     * bodies whose {@code BodyGen} locals start above slot 2, so slot 2 always holds the path.
     */
    private void emitConstructCall(CodeBuilder code, AstExpressions gen, Hir.Construct construct,
                                   SequencedMap<String, Type> fields) {
        // The decoder is still AST-level; elaborate its field inits so the shared emitFieldValues
        // consumes one representation, with the type the checker decides for each (ADR-0021, #81).
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
        // Souther construction Result -> Raoh boundary Result. An invariant failure becomes a
        // Raoh failure (spec §violation-destination, §decoder-role); success wraps the constructed value.
        //
        // The failure names the clause that did not hold, and it travels in the metadata beside the
        // rejecting type: with the code the shared one, that metadata is all a resolver has to go on.
        // The message is the default, so a resolver may still replace it.
        int srSlot = gen.slot(Type.STRING);
        code.astore(srSlot);
        code.aload(srSlot);
        code.instanceOf(CD_ResultErr);
        Label okL = code.newLabel();
        code.ifeq(okL);
        int failure = gen.slot(Type.STRING);
        code.aload(srSlot);
        code.checkcast(CD_ResultErr);
        code.invokevirtual(CD_ResultErr, "error", MTD_error);
        code.checkcast(CD_InvariantFailure);
        code.astore(failure);
        // the path this value was decoded at (spec §violation-destination, §case-propagation) —
        // not the document root
        code.aload(2);
        code.loadConstant("invariant_violation");
        code.aload(failure);
        code.invokevirtual(CD_InvariantFailure, "toString", MethodTypeDesc.of(CD_String));
        code.aload(failure);
        code.invokevirtual(CD_InvariantFailure, "meta", MTD_failureMeta);
        code.invokestatic(CD_RResult, "fail", MTD_Rfail4, true);
        code.areturn();
        code.labelBinding(okL);
        code.aload(srSlot);
        code.checkcast(CD_ResultOk);
        code.invokevirtual(CD_ResultOk, "value", MTD_Object);
        code.invokestatic(CD_RResult, "ok", MTD_Rok, true);
        code.areturn();
    }

    byte[] generateEncoderClass(ClassDesc cdName, Hir.Data data, Hir.EncoderDef enc) {
        ClassDesc cdEnc = cd(new GeneratedClass.Encoder(valueOf(data)));
        return build(cdEnc, cb -> {
            cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withInterfaceSymbols(CD_REncoder);
            emitDefaultCtor(cb);
            emitSharedInstance(cb, cdEnc);
            cb.withMethodBody("encode", MTD_Rencode, ClassFile.ACC_PUBLIC, code -> {
                AstExpressions gen = new AstExpressions(new BodyGen(ctx, code, data, cdName, 2));
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
                code.invokestatic(CD_Representations, "canonicalNumber", MTD_canonicalNumber);
            }
            case Hir.IsoTextRaw t -> {
                gen.expr(t.arg());
                code.invokevirtual(CD_Object, "toString", MethodTypeDesc.of(CD_String));
            }
            case Hir.EncodeRaw e -> {
                invokeCodec(code, e.typeName(), "encoder", MTD_Rencoder);
                gen.expr(e.arg());
                code.invokeinterface(CD_REncoder, "encode", MTD_Rencode);
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
                code.invokestatic(CD_MapEncoders, "list", MTD_Rencode_list);
                gen.expr(le.source());
                code.invokeinterface(CD_REncoder, "encode", MTD_Rencode);
            }
            case Hir.SetEnc se -> {
                pushElemEncoder(code, se.elem());
                code.invokestatic(CD_MapEncoders, "list", MTD_Rencode_list);   // Encoder for an array
                gen.expr(se.source());                                          // the Set value
                code.invokestatic(CD_Sets, "toList", MethodTypeDesc.of(CD_List, CD_Set));   // Set -> List
                code.invokeinterface(CD_REncoder, "encode", MTD_Rencode);      // encode the array
                code.invokestatic(CD_Representations, "sortedArray", MTD_Representations_sorted);
            }
            case Hir.MapEnc me -> {
                pushElemEncoder(code, me.elem());
                code.invokestatic(CD_MapEncoders, "mapOf", MTD_Rencode_list);   // Encoder<Map<String,V>,Object>
                gen.expr(me.source());                                          // Map<K,V>
                if (needsKeyRender(me.key())) {
                    // Render the keys bare before the String-keyed map encoder.
                    pushKeyRenderer(code, me.key());                            // Function<K,String>
                    code.invokestatic(CD_Maps, "mapKeys", MTD_mapKeys);         // Map<String,V>
                }
                code.invokeinterface(CD_REncoder, "encode", MTD_Rencode);
                code.invokestatic(CD_Representations, "sortedObject", MTD_Representations_sorted);
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

    /** Pushes a Raoh {@link net.unit8.raoh.encode.Encoder} for a list/set/map element. A nested
     * collection composes the same combinators the field encoders use, so a
     * {@code Map<String, List<商品ID>>} encodes as {@code mapOf(list(商品ID.encoder()))}. Set and
     * newtype-keyed Map are not Raoh shapes on their own — they are the list / String-keyed map
     * encoder with the value converted first, which {@code contramap} does. */
    private void pushElemEncoder(CodeBuilder code, Hir.EncElem elem) {
        switch (elem) {
            case Hir.PrimEnc p -> {
                code.invokestatic(CD_ObjectEncoders, leafEncoderName(p.kind()), MTD_Rencode_leaf);
                canonicalizeAmount(code, p.kind());
            }
            case Hir.DataEnc d -> invokeCodec(code, d.typeName(), "encoder", MTD_Rencoder);
            case Hir.ListElemEnc l -> {
                pushElemEncoder(code, l.elem());
                code.invokestatic(CD_MapEncoders, "list", MTD_Rencode_list);
            }
            case Hir.SetElemEnc s -> {
                pushElemEncoder(code, s.elem());
                code.invokestatic(CD_MapEncoders, "list", MTD_Rencode_list);
                code.invokedynamic(setToListCallSite());                    // Function<Set, List>
                code.invokeinterface(CD_REncoder, "contramap", MTD_Rencoder_contramap);
                code.invokedynamic(orderingCallSite("sortedArray"));        // Encoder<Object, Object>
                code.invokeinterface(CD_REncoder, "andThen", MTD_Rencoder_andThen);
            }
            // no key to omit here, so an absent member is written null
            case Hir.OptionElemEnc o -> {
                pushElemEncoder(code, o.elem());                            // Encoder<T, Object>
                code.invokedynamic(encodeAsFunctionCallSite());             // Function<T, Object>
                code.invokedynamic(optionElemEncoderCallSite());            // Encoder<Option<T>, Object>
            }
            case Hir.MapElemEnc m -> {
                pushElemEncoder(code, m.value());
                code.invokestatic(CD_MapEncoders, "mapOf", MTD_Rencode_list);
                if (needsKeyRender(m.key())) {
                    pushKeyRenderer(code, m.key());                         // Function<K, String>
                    code.invokedynamic(mapKeysCallSite());                  // Function<Map<K,V>, Map<String,V>>
                    code.invokeinterface(CD_REncoder, "contramap", MTD_Rencoder_contramap);
                }
                code.invokedynamic(orderingCallSite("sortedObject"));       // Encoder<Object, Object>
                code.invokeinterface(CD_REncoder, "andThen", MTD_Rencoder_andThen);
            }
        }
    }

    /**
     * A leaf encoder for a {@code Decimal}, followed by the amount's own form. Raoh's {@code decimal}
     * hands the {@code BigDecimal} through as it is, scale and all, and the scale is how a number was
     * written rather than how much it is.
     */
    private static void canonicalizeAmount(CodeBuilder code, LeafScalar kind) {
        if (kind != LeafScalar.DECIMAL) {
            return;
        }
        code.invokedynamic(canonicalNumberCallSite());
        code.invokeinterface(CD_REncoder, "andThen", MTD_Rencoder_andThen);
    }

    /** {@code Representations::canonicalNumber} as an {@code Encoder}. */
    private static DynamicCallSiteDesc canonicalNumberCallSite() {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, CD_Representations, "canonicalNumber",
                MTD_canonicalNumber);
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
    private static DynamicCallSiteDesc orderingCallSite(String ordering) {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, CD_Representations, ordering,
                MTD_Representations_sorted);
        return Lambdas.callSite(Lambdas.Sam.ENCODER, impl, MTD_Representations_sorted);
    }

    /** {@code Option::ofNullable} as a {@code Function}, for {@code Decoder.map} to lift a
     *  null-tolerant decoder's answer into an {@code Option}. */
    private static DynamicCallSiteDesc optionOfNullableCallSite() {
        // Option is a sealed interface, so its static factory is an interface method reference
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.INTERFACE_STATIC, CD_Option, "ofNullable", MTD_ofNullable);
        return Lambdas.callSite(Lambdas.Sam.FUNCTION, impl, MTD_ofNullable);
    }

    /** An {@code Encoder}'s own {@code encode} as a {@code Function}, capturing the encoder already
     *  on the stack. The kernel does not know the boundary library's types, so what it is handed is
     *  a function rather than an encoder ({@code Options.encodedOrNull}). */
    private static DynamicCallSiteDesc encodeAsFunctionCallSite() {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.INTERFACE_VIRTUAL, CD_REncoder, "encode", MTD_Rencode);
        return Lambdas.callSite(Lambdas.Sam.FUNCTION, impl, MTD_Rencode,
                CD_REncoder);                                            // captures the encoder
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
    private static DynamicCallSiteDesc setToListCallSite() {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, CD_Sets, "toList", MTD_Sets_toList);
        return Lambdas.callSite(Lambdas.Sam.FUNCTION, impl, MTD_Sets_toList);
    }

    /** {@code m -> Maps.mapKeysWith(keyFn, m)} as a {@code Function}, capturing the key function
     * already on the stack: a nested newtype-keyed Map renders its keys bare before the String-keyed
     * map encoder sees it. */
    private static DynamicCallSiteDesc mapKeysCallSite() {
        DirectMethodHandleDesc impl = MethodHandleDesc.ofMethod(
                DirectMethodHandleDesc.Kind.STATIC, CD_Maps, "mapKeysWith", MTD_mapKeysWith);
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
            cb.withFlags(ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withInterfaceSymbols(CD_REncoder);
            emitDefaultCtor(cb);
            emitSharedInstance(cb, cdEnc);
            cb.withMethodBody("encode", MTD_Rencode, ClassFile.ACC_PUBLIC, code -> {
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
            code.invokeinterface(CD_REncoder, "encode", MTD_Rencode);
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

    /** Pushes the encoder a member writes itself with: its own derived one, or the Raoh leaf encoder
     * for a primitive, which declares none. */
    private void pushMemberEncoder(CodeBuilder code, TypeSymbol member) {
        if (member.isPrimitive()) {
            LeafScalar scalar = memberScalar(member);
            code.invokestatic(CD_ObjectEncoders, leafEncoderName(scalar), MTD_Rencode_leaf);
            canonicalizeAmount(code, scalar);
            return;
        }
        // a member is one of the union's effective members, every named sum already expanded to its
        // leaves (spec §jvm-product), so its encoder() is on a class and never on a sealed interface
        code.invokestatic(cd(member), "encoder", MTD_Rencoder, false);
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
        emitCodecFactory(cb, "encoder", CD_REncoder, cd(new GeneratedClass.Encoder(union)),
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

    /** The Raoh {@code ObjectEncoders} leaf method for each primitive (matches the leaf decoders). */
    private static String leafEncoderName(LeafScalar kind) {
        return switch (kind) {
            case STRING -> "string";
            case INT -> "long_";
            case BOOL -> "bool";
            case DECIMAL -> "decimal";
            case DATE -> "date";
            case TIME -> "time";
            case DATETIME -> "dateTime";
            case INSTANT -> "iso8601";
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
