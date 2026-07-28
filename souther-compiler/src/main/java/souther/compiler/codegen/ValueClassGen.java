package souther.compiler.codegen;

import souther.compiler.check.Symbols;
import souther.compiler.ast.Ast;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.check.TypeOps;

import java.lang.classfile.Attribute;
import java.lang.classfile.ClassBuilder;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassSignature;
import java.lang.classfile.CodeBuilder;
import java.lang.classfile.Label;
import java.lang.classfile.MethodSignature;
import java.lang.classfile.Signature;
import java.lang.classfile.TypeAnnotation;
import java.lang.classfile.attribute.PermittedSubclassesAttribute;
import java.lang.classfile.attribute.RecordAttribute;
import java.lang.classfile.attribute.RecordComponentInfo;
import java.lang.classfile.attribute.RuntimeVisibleTypeAnnotationsAttribute;
import java.lang.classfile.attribute.SignatureAttribute;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static souther.compiler.codegen.Descriptors.*;
import static souther.compiler.codegen.JvmTypes.*;

/**
 * Generates a data/sum/unit value class: its fields, package-private constructor, accessors, value
 * equality/hashCode, and the invariant-checking {@code __construct} (spec 7, 19). Each type's codecs
 * are emitted by the {@link CodecGen} it holds; body expressions through a {@link BodyGen} built per
 * method.
 */
final class ValueClassGen {

    private final CodegenContext ctx;
    private final String pkg;
    private final Symbols symbols;
    private final CodecGen codec;

    ValueClassGen(CodegenContext ctx, CodecGen codec) {
        this.ctx = ctx;
        this.pkg = ctx.pkg;
        this.symbols = ctx.symbols;
        this.codec = codec;
    }

    private ClassDesc cd(String typeName) { return ctx.cd(typeName); }
    private ClassDesc cd(TypeName typeName) { return ctx.cd(typeName); }
    private ClassDesc[] caseInterfaces(String name) { return ctx.caseInterfaces(name); }
    private Map<String, Type> fieldTypes(Ast.Data data) { return ctx.fieldTypes(data); }
    private int pub(String name) { return ctx.pub(name); }
    private ClassDesc jvmType(Type type) { return JvmTypes.jvmType(type, ctx); }
    private ClassDesc[] fieldDescs(Map<String, Type> fields) { return JvmTypes.fieldDescs(fields, ctx); }

    void generateData(Ast.Data data, Map<String, byte[]> out) {
        ClassDesc cdName = cd(data.name());
        Map<String, Type> fields = fieldTypes(data);

        out.put(pkg + "." + data.name(), build(cdName, cb -> {
            cb.withFlags(pub(data.name()) | ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withSuperclass(CD_Record);
            cb.with(recordComponents(fields));
            List<ClassDesc> ifaces = new ArrayList<>(List.of(caseInterfaces(data.name())));
            boolean ordered = isOrderedNewtype(data, fields);
            if (ordered) {
                ifaces.add(CD_Comparable);
            }
            if (!ifaces.isEmpty()) {
                cb.withInterfaceSymbols(ifaces);
            }
            if (ordered) {
                cb.with(SignatureAttribute.of(ClassSignature.parseFrom(classSignature(cdName, ifaces))));
            }
            for (Map.Entry<String, Type> f : fields.entrySet()) {
                emitField(cb, f.getKey(), f.getValue());
            }
            emitCtor(cb, cdName, fields);
            emitValueEquality(cb, cdName, fields);
            emitToString(cb, cdName, data.name(), fields);
            if (ordered) {
                emitCompareTo(cb, cdName, fields.entrySet().iterator().next());
            }
            emitConstructMethod(cb, cdName, data, fields);
            emitAccessors(cb, cdName, fields);
            data.decoder().ifPresent(d -> {
                boolean mapInput = codec.isMapInput(data.name());
                codec.emitFactory(cb, "decoder", CD_RDecoder, data, "$Dec");
                if (codec.jsonCompatible(data.name())) codec.emitSourceFactory(cb, data.name(), CodecGen.Src.JSON, mapInput);
                if (codec.recordCompatible(data.name())) codec.emitSourceFactory(cb, data.name(), CodecGen.Src.JOOQ, mapInput);
            });
            data.encoder().ifPresent(e -> codec.emitFactory(cb, "encoder", CD_REncoder, data, "$Enc"));
        }));

        data.decoder().ifPresent(dec -> {
            out.put(pkg + "." + data.name() + "$Dec",
                    codec.generateDecoderClass(cdName, data, dec, fields, CodecGen.Src.NEUTRAL));
            if (codec.jsonCompatible(data.name())) {
                out.put(pkg + "." + data.name() + "$DecJson",
                        codec.generateDecoderClass(cdName, data, dec, fields, CodecGen.Src.JSON));
            }
            if (codec.recordCompatible(data.name())) {
                out.put(pkg + "." + data.name() + "$DecRecord",
                        codec.generateDecoderClass(cdName, data, dec, fields, CodecGen.Src.JOOQ));
            }
        });
        data.encoder().ifPresent(enc ->
                out.put(pkg + "." + data.name() + "$Enc", codec.generateEncoderClass(cdName, data, enc)));

        // A helper for an invariant-bearing newtype: a Raoh-free `boolean check(value)` that runs the
        // same invariant bytecode as __construct (via gen.expr). Two callers: a constant construction
        // is verified at compile time through it — 金額(-5) is a compile error, not a runtime abort
        // (ADR-0032) — and the derived decoder passes it to Raoh's `refine` for an invariant no
        // constraint states exactly (issue #83).
        if (data.newtype() && !TypeOps.effectiveInvariants(data, symbols).isEmpty()) {
            emitCtfeCheck(data, fields, out);
        }
    }

    private void emitCtfeCheck(Ast.Data data, Map<String, Type> fields, Map<String, byte[]> out) {
        ClassDesc cdName = cd(data.name());
        ClassDesc cdCtfe = cd(data.name() + "$Ctfe");
        out.put(pkg + "." + data.name() + "$Ctfe", build(cdCtfe, cb -> {
            cb.withFlags(ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            cb.withMethodBody("check", MethodTypeDesc.of(ConstantDescs.CD_boolean, fieldDescs(fields)),
                    ClassFile.ACC_STATIC | ClassFile.ACC_PUBLIC, code -> {
                        BodyGen gen = new BodyGen(ctx, code, data, cdName, 0);
                        int slot = 0;
                        for (Map.Entry<String, Type> f : fields.entrySet()) {
                            gen.bind(f.getKey(), slot, f.getValue());
                            slot += width(f.getValue());
                        }
                        for (Ast.Expr inv : TypeOps.effectiveInvariants(data, symbols)) {
                            gen.expr(inv);                 // the same boolean __construct checks
                            Label ok = code.newLabel();
                            code.ifne(ok);
                            code.iconst_0();
                            code.ireturn();                // an invariant is false
                            code.labelBinding(ok);
                        }
                        code.iconst_1();
                        code.ireturn();                    // all held
                    });
        }));
    }

    void generateSum(Ast.SumData sum, Map<String, byte[]> out) {
        ClassDesc cdX = cd(sum.name());
        List<ClassDesc> caseCds = new ArrayList<>();
        for (Ast.Name caseName : sum.cases()) {
            caseCds.add(cd(caseName.denotes()));
        }
        out.put(pkg + "." + sum.name(), build(cdX, cb -> {
            cb.withFlags(pub(sum.name()) | ClassFile.ACC_INTERFACE | ClassFile.ACC_ABSTRACT);
            // A sum may itself be a case of another sum (spec 8.3), and then it carries that sum's
            // interface as a product or unit case does. Only the direct link is recorded, which is
            // all that is needed: interface inheritance carries it the rest of the way, so a leaf of
            // this sum is a value of the outer one without being named there.
            ClassDesc[] ifaces = caseInterfaces(sum.name());
            if (ifaces.length > 0) {
                cb.withInterfaceSymbols(ifaces);
            }
            cb.with(PermittedSubclassesAttribute.ofSymbols(caseCds));
            sum.decoder().ifPresent(disc -> {
                codec.emitCodecFactory(cb, "decoder", CD_RDecoder, cd(sum.name() + "$Dec"), CodecGen.decoderSig(cdX, true));
                if (codec.jsonCompatible(sum.name())) codec.emitSourceFactory(cb, sum.name(), CodecGen.Src.JSON, true);
                if (codec.recordCompatible(sum.name())) codec.emitSourceFactory(cb, sum.name(), CodecGen.Src.JOOQ, true);
            });
            sum.encoder().ifPresent(enc ->
                    codec.emitCodecFactory(cb, "encoder", CD_REncoder, cd(sum.name() + "$Enc"),
                            CodecGen.encoderSig(cdX, CD_Map)));
        }));
        sum.decoder().ifPresent(disc -> {
            out.put(pkg + "." + sum.name() + "$Dec", codec.generateSumDecoder(sum, disc, CodecGen.Src.NEUTRAL));
            if (codec.jsonCompatible(sum.name())) {
                out.put(pkg + "." + sum.name() + "$DecJson", codec.generateSumDecoder(sum, disc, CodecGen.Src.JSON));
            }
            if (codec.recordCompatible(sum.name())) {
                out.put(pkg + "." + sum.name() + "$DecRecord", codec.generateSumDecoder(sum, disc, CodecGen.Src.JOOQ));
            }
        });
        sum.encoder().ifPresent(enc ->
                out.put(pkg + "." + sum.name() + "$Enc", codec.generateSumEncoder(sum, enc)));
    }

    void generateUnit(Ast.UnitData unit, Map<String, byte[]> out) {
        ClassDesc cdU = cd(unit.name());
        ClassDesc cdDec = cd(unit.name() + "$Dec");
        ClassDesc cdEnc = cd(unit.name() + "$Enc");
        out.put(pkg + "." + unit.name(), build(cdU, cb -> {
            cb.withFlags(pub(unit.name()) | ClassFile.ACC_FINAL | ClassFile.ACC_SUPER);
            // a unit is a field-less data, so it is a record with no components: `case 承認済み()`
            // deconstructs it in a Java switch as its sibling product cases do (spec 19.2)
            cb.withSuperclass(CD_Record);
            cb.with(recordComponents(Map.of()));
            ClassDesc[] ifaces = caseInterfaces(unit.name());
            if (ifaces.length > 0) {
                cb.withInterfaceSymbols(ifaces);
            }
            emitDefaultCtor(cb, CD_Record);
            emitValueEquality(cb, cdU, Map.of());   // all units of a type are the same value
            emitToString(cb, cdU, unit.name(), Map.of());
            // A unit has no fields, no invariant and so no `__construct` (spec §unit-data), so the
            // type has exactly one value. The field is public because another module's generated
            // code loads it, and on an exposed unit that puts the value within reach of hand-written
            // Java too — which costs nothing a unit was protecting: it carries no invariant, and
            // construction is governed by `constructs` rather than by visibility (ADR-0059).
            emitSharedInstance(cb, cdU);
            // a unit is a field-less data: its codec reads/writes nothing but the tag the sum adds
            // A unit ignores its input, so it decodes from every source. Generate all three so
            // unit cases of a JSON/record sum have a matching decoder to dispatch to.
            codec.emitCodecFactory(cb, "decoder", CD_RDecoder, cdDec, CodecGen.decoderSig(cdU, false));
            codec.emitCodecFactory(cb, "jsonDecoder", CD_RDecoder, cd(unit.name() + "$DecJson"),
                    CodecGen.decoderSigFor(CodecGen.Src.JSON, cdU, false));
            codec.emitCodecFactory(cb, "recordDecoder", CD_RDecoder, cd(unit.name() + "$DecRecord"),
                    CodecGen.decoderSigFor(CodecGen.Src.JOOQ, cdU, false));
            codec.emitCodecFactory(cb, "encoder", CD_REncoder, cdEnc, CodecGen.encoderSig(cdU, CD_Map));
        }));
        out.put(pkg + "." + unit.name() + "$Dec", codec.generateUnitDecoder(cdU, cdDec));
        out.put(pkg + "." + unit.name() + "$DecJson", codec.generateUnitDecoder(cdU, cd(unit.name() + "$DecJson")));
        out.put(pkg + "." + unit.name() + "$DecRecord", codec.generateUnitDecoder(cdU, cd(unit.name() + "$DecRecord")));
        out.put(pkg + "." + unit.name() + "$Enc", codec.generateUnitEncoder(cdEnc));
    }

    /**
     * Emits {@code equals} / {@code hashCode} comparing every field.
     *
     * <p>A data is an immutable value, so two of them are the same when their fields are — which
     * is what {@code ==} means on a data (spec 16.2) and what Java callers expect of a value
     * class. A unit data has no fields, so all of its values are equal.
     */
    private void emitValueEquality(ClassBuilder cb, ClassDesc cdName, Map<String, Type> fields) {
        cb.withMethodBody("equals", MethodTypeDesc.of(ConstantDescs.CD_boolean, CD_Object),
                ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL, code -> {
                    Label same = code.newLabel();
                    Label differs = code.newLabel();
                    code.aload(0);
                    code.aload(1);
                    code.if_acmpeq(same);
                    code.aload(1);
                    code.instanceOf(cdName);
                    code.ifeq(differs);
                    if (!fields.isEmpty()) {
                        code.aload(1);
                        code.checkcast(cdName);
                        code.astore(2);
                        for (Map.Entry<String, Type> f : fields.entrySet()) {
                            Type t = f.getValue();
                            code.aload(0);
                            code.getfield(cdName, f.getKey(), jvmType(t));
                            code.aload(2);
                            code.getfield(cdName, f.getKey(), jvmType(t));
                            if (t == Type.INT) {
                                code.lcmp();
                                code.ifne(differs);
                            } else if (t == Type.BOOL) {
                                code.if_icmpne(differs);
                            } else if (t == Type.DECIMAL) {
                                emitDecimalEquals(code);   // by value, not by scale (spec 7.1)
                                code.ifeq(differs);
                            } else {
                                code.invokestatic(CD_Objects, "equals", MTD_Objects_equals);
                                code.ifeq(differs);
                            }
                        }
                    }
                    code.labelBinding(same);
                    code.iconst_1();
                    code.ireturn();
                    code.labelBinding(differs);
                    code.iconst_0();
                    code.ireturn();
                });

        cb.withMethodBody("hashCode", MethodTypeDesc.of(ConstantDescs.CD_int),
                ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL, code -> {
                    code.iconst_1();
                    for (Map.Entry<String, Type> f : fields.entrySet()) {
                        Type t = f.getValue();
                        code.loadConstant(31);
                        code.imul();
                        code.aload(0);
                        code.getfield(cdName, f.getKey(), jvmType(t));
                        if (t == Type.INT) {
                            code.invokestatic(CD_Long, "hashCode", MTD_Long_hashCode);
                        } else if (t == Type.BOOL) {
                            // already an int 0/1
                        } else if (t == Type.DECIMAL) {
                            // equality ignores scale, so the hash must too, or 1.0 and 1.00 land
                            // in different buckets and a Map keyed by this data stops working.
                            // Groovy changed `==` and left hashCode alone; that bug is still open.
                            code.invokevirtual(CD_BigDecimal, "stripTrailingZeros", MTD_BD_strip);
                            code.invokestatic(CD_Objects, "hashCode", MTD_Objects_hashCode);
                        } else {
                            code.invokestatic(CD_Objects, "hashCode", MTD_Objects_hashCode);
                        }
                        code.iadd();
                    }
                    code.ireturn();
                });
    }

    /** A single-value newtype over an ordered type — ordered by the value it wraps (ADR-0047), which
     * the class carries as {@link Comparable} so {@code sort} / {@code max} / {@code min} compare it
     * by natural order, and a Java reader can put it in a {@code TreeSet}. */
    private boolean isOrderedNewtype(Ast.Data data, Map<String, Type> fields) {
        return data.newtype() && fields.size() == 1
                && TypeOps.isOrderedValue(fields.values().iterator().next(), symbols);
    }

    /** {@code Record} plus each interface, with {@code Comparable} bound to the class itself, so a
     * Java reader sees {@code Comparable<金額>} rather than the raw form. */
    private static String classSignature(ClassDesc cdName, List<ClassDesc> ifaces) {
        StringBuilder sig = new StringBuilder(CD_Record.descriptorString());
        for (ClassDesc iface : ifaces) {
            if (iface.equals(CD_Comparable)) {
                String raw = CD_Comparable.descriptorString();
                sig.append(raw, 0, raw.length() - 1)      // drop the ';' to insert the type argument
                        .append('<').append(cdName.descriptorString()).append(">;");
            } else {
                sig.append(iface.descriptorString());
            }
        }
        return sig.toString();
    }

    /**
     * Emits {@code toString} in the form a record prints — {@code 金額[value=500]}, the type name and
     * each component. {@code java.lang.Record} declares it abstract, so a data without one resolves to
     * that declaration and throws {@code AbstractMethodError} when anything prints the value.
     */
    private void emitToString(ClassBuilder cb, ClassDesc cdName, String typeName,
                              Map<String, Type> fields) {
        cb.withMethodBody("toString", MTD_toString, ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL, code -> {
            code.new_(CD_StringBuilder);
            code.dup();
            code.invokespecial(CD_StringBuilder, "<init>", MTD_void);
            append(code, typeName + "[");
            boolean first = true;
            for (Map.Entry<String, Type> f : fields.entrySet()) {
                append(code, (first ? "" : ", ") + f.getKey() + "=");
                first = false;
                Type t = f.getValue();
                code.aload(0);
                code.getfield(cdName, f.getKey(), jvmType(t));
                if (t == Type.INT) {
                    code.invokevirtual(CD_StringBuilder, "append", MTD_SB_appendLong);
                } else if (t == Type.BOOL) {
                    code.invokevirtual(CD_StringBuilder, "append", MTD_SB_appendBoolean);
                } else {
                    code.invokevirtual(CD_StringBuilder, "append", MTD_SB_appendObject);
                }
            }
            append(code, "]");
            code.invokevirtual(CD_StringBuilder, "toString", MTD_toString);
            code.areturn();
        });
    }

    /** Appends a literal to the {@code StringBuilder} on the stack, leaving it there. */
    private static void append(CodeBuilder code, String literal) {
        code.loadConstant(literal);
        code.invokevirtual(CD_StringBuilder, "append", MTD_SB_appendString);
    }

    /**
     * Emits {@code compareTo}: an {@code Int} newtype compares its {@code long} carrier, any other
     * ordered value is itself {@link Comparable} — a {@code String} / {@code BigDecimal} /
     * {@code LocalDate} / {@code LocalDateTime}, or a newtype over one, which carries its own
     * {@code compareTo}. The erased {@code compareTo(Object)} bridge is what the runtime's
     * natural-order compare calls.
     */
    private void emitCompareTo(ClassBuilder cb, ClassDesc cdName, Map.Entry<String, Type> value) {
        ClassDesc fd = jvmType(value.getValue());
        cb.withMethodBody("compareTo", MethodTypeDesc.of(ConstantDescs.CD_int, cdName),
                ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL, code -> {
                    code.aload(0);
                    code.getfield(cdName, value.getKey(), fd);
                    code.aload(1);
                    code.getfield(cdName, value.getKey(), fd);
                    if (value.getValue() == Type.INT) {
                        code.lcmp();   // -1 / 0 / 1, which is compareTo's contract
                    } else {
                        code.invokeinterface(CD_Comparable, "compareTo", MTD_compareTo_Object);
                    }
                    code.ireturn();
                });
        cb.withMethodBody("compareTo", MethodTypeDesc.of(ConstantDescs.CD_int, CD_Object),
                ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL
                        | ClassFile.ACC_BRIDGE | ClassFile.ACC_SYNTHETIC, code -> {
                    code.aload(0);
                    code.aload(1);
                    code.checkcast(cdName);
                    code.invokevirtual(cdName, "compareTo", MethodTypeDesc.of(ConstantDescs.CD_int, cdName));
                    code.ireturn();
                });
    }

    /**
     * Emits the public record-style read accessor {@code <field>()} for each component (spec 8.5,
     * 19.2). Every data has them, not only an exposed one: a component of the {@code Record} attribute
     * is read through its accessor, the generated code of this module reads a field the same way, and
     * a class the module keeps to itself is out of a Java caller's reach anyway. Reading never enables
     * construction — the constructor stays non-public (spec 2.7).
     *
     * <p>The return type carries {@code @NonNull} because Kotlin types a component from the record and
     * does not apply the class's {@code @NullMarked} there; without it every read is a platform type
     * again (spec §jvm-nullness).
     */
    private void emitAccessors(ClassBuilder cb, ClassDesc cdName, Map<String, Type> fields) {
        for (Map.Entry<String, Type> f : fields.entrySet()) {
            Type ft = f.getValue();
            ClassDesc fd = jvmType(ft);
            String sig = JvmTypes.genericSig(ft, ctx);
            List<TypeAnnotation> nonNull =
                    JvmTypes.nonNullPositions(ft, TypeAnnotation.TargetInfo.ofMethodReturn());
            cb.withMethod(f.getKey(), MethodTypeDesc.of(fd),
                    ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL, mb -> {
                        if (sig != null) mb.with(SignatureAttribute.of(MethodSignature.parseFrom("()" + sig)));
                        if (!nonNull.isEmpty()) {
                            mb.with(RuntimeVisibleTypeAnnotationsAttribute.of(nonNull));
                        }
                        mb.withCode(code -> {
                            code.aload(0);
                            code.getfield(cdName, f.getKey(), fd);
                            if (ft == Type.INT) {
                                code.lreturn();
                            } else if (ft == Type.BOOL) {
                                code.ireturn();
                            } else {
                                code.areturn();
                            }
                        });
                    });
        }
    }

    /**
     * The {@code Record} attribute naming each field as a component, in constructor order, so the
     * class is a record to everything that reads class files: javac deconstructs it in a record
     * pattern, Kotlin reads each component as a property, and {@code Class.getRecordComponents}
     * answers (spec 19.2). Each component repeats what its accessor states — a container's generic
     * {@code Signature}, and {@code @NonNull} — because reflection reads the component, not the
     * accessor.
     */
    private RecordAttribute recordComponents(Map<String, Type> fields) {
        List<RecordComponentInfo> components = new ArrayList<>();
        for (Map.Entry<String, Type> f : fields.entrySet()) {
            Type type = f.getValue();
            String sig = JvmTypes.genericSig(type, ctx);
            List<Attribute<?>> attrs = new ArrayList<>();
            if (sig != null) attrs.add(SignatureAttribute.of(Signature.parseFrom(sig)));
            List<TypeAnnotation> nonNull =
                    JvmTypes.nonNullPositions(type, TypeAnnotation.TargetInfo.ofField());
            if (!nonNull.isEmpty()) attrs.add(RuntimeVisibleTypeAnnotationsAttribute.of(nonNull));
            components.add(RecordComponentInfo.of(f.getKey(), jvmType(type), attrs));
        }
        return RecordAttribute.of(components);
    }

    /**
     * Emits a {@code private final} backing field, as a record's is: every read goes through the
     * accessor, including the generated code of this module. A container field
     * ({@code List}/{@code Set}/{@code Map}/{@code Option}) also gets a generic {@code Signature} so
     * its element type survives to a Java reader; a field whose raw descriptor already names it fully
     * gets none.
     */
    private void emitField(ClassBuilder cb, String name, Type type) {
        String sig = JvmTypes.genericSig(type, ctx);
        cb.withField(name, jvmType(type), fb -> {
            fb.withFlags(ClassFile.ACC_PRIVATE | ClassFile.ACC_FINAL);
            if (sig != null) fb.with(SignatureAttribute.of(Signature.parseFrom(sig)));
        });
    }

    /**
     * Emits the canonical constructor: the components in declaration order, package-private, so a
     * value is built inside the module or through the invariant-checking {@code __construct} and not
     * by a Java caller writing {@code new} (spec 8.5).
     */
    private void emitCtor(ClassBuilder cb, ClassDesc cdName, Map<String, Type> fields) {
        cb.withMethodBody("<init>", MethodTypeDesc.of(ConstantDescs.CD_void, fieldDescs(fields)), 0, code -> {
            code.aload(0);
            code.invokespecial(CD_Record, "<init>", MTD_void);
            int slot = 1;
            for (Map.Entry<String, Type> f : fields.entrySet()) {
                code.aload(0);
                load(code, slot, f.getValue());
                code.putfield(cdName, f.getKey(), jvmType(f.getValue()));
                slot += width(f.getValue());
            }
            code.return_();
        });
    }

    private void emitConstructMethod(ClassBuilder cb, ClassDesc cdName, Ast.Data data,
                                     Map<String, Type> fields) {
        // Public for an exposed type: a behavior of another module may declare `constructs T`
        // (ADR-0002 never restricted that to T's own module), and this is the path it takes — the one
        // that runs the invariant. A type this module keeps to itself keeps its entry package-private.
        cb.withMethod("__construct", MethodTypeDesc.of(CD_Result, fieldDescs(fields)),
                ClassFile.ACC_STATIC | ctx.pub(data.name()), mb -> {
                    mb.with(SignatureAttribute.of(
                            MethodSignature.parseFrom(constructSignature(fields, cdName))));
                    mb.withCode(code -> {
                        BodyGen gen = new BodyGen(ctx, code, data, cdName, 0);
                        int slot = 0;
                        for (Map.Entry<String, Type> f : fields.entrySet()) {
                            gen.bind(f.getKey(), slot, f.getValue());
                            slot += width(f.getValue());
                        }

                        for (Ast.Expr inv : TypeOps.effectiveInvariants(data, symbols)) {
                            gen.expr(inv);
                            Label ok = code.newLabel();
                            code.ifne(ok);
                            code.loadConstant("invariant violated on " + data.name());
                            code.invokestatic(CD_Result, "err", MTD_Result_err, true);
                            code.areturn();
                            code.labelBinding(ok);
                        }

                        code.new_(cdName);
                        code.dup();
                        int s = 0;
                        for (Map.Entry<String, Type> f : fields.entrySet()) {
                            load(code, s, f.getValue());
                            s += width(f.getValue());
                        }
                        code.invokespecial(cdName, "<init>",
                                MethodTypeDesc.of(ConstantDescs.CD_void, fieldDescs(fields)));
                        code.invokestatic(CD_Result, "ok", MTD_Result_Object, true);
                        code.areturn();
                    });
                });
    }

    /**
     * The generic {@code Signature} of {@code __construct}: {@code Result<T, String>}, where the
     * failure side is the invariant message this method builds. Unlike a factory's, it is written
     * whether or not a field is a container — the raw {@code Result} the descriptor names carries no
     * type at all, and a Kotlin caller reads a raw type as a platform type, which is the one thing
     * the rest of the class is marked to avoid (issue #150).
     */
    private String constructSignature(Map<String, Type> fields, ClassDesc cdName) {
        StringBuilder sb = new StringBuilder("(");
        for (Type t : fields.values()) {
            String g = JvmTypes.genericSig(t, ctx);
            sb.append(g != null ? g : jvmType(t).descriptorString());
        }
        return sb.append(")Lsouther/runtime/Result<")
                .append(cdName.descriptorString())
                .append(CD_String.descriptorString())
                .append(">;").toString();
    }
}
