package souther.compiler.codegen;

import java.lang.classfile.Annotation;
import java.lang.classfile.ClassBuilder;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassHierarchyResolver;
import java.lang.classfile.attribute.RuntimeVisibleAnnotationsAttribute;
import java.lang.classfile.attribute.SourceFileAttribute;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.MethodHandleDesc;
import java.lang.constant.MethodTypeDesc;
import java.util.function.Consumer;

/**
 * The JVM class and method descriptors the backend emits against (spec sections 19, 20). These name
 * the runtime classes ({@code Result}/{@code Behavior}/{@code Maps}/{@code Sets}/...), the Raoh
 * decode/encode targets (spec 10.6), and the boxed-primitive and collection interfaces. Shared by
 * every generator in this package; a call site references one through a static import.
 */
final class Descriptors {

    private Descriptors() {
    }

    // Generated classes aren't loadable while we compile, so stack-map merging (e.g. an
    // `if` producing a union of two data types) can't resolve their common supertype.
    // Treat any class we can't resolve as a plain class extending Object.
    private static final ClassFile CF = ClassFile.of(ClassFile.ClassHierarchyResolverOption.of(
            desc -> {
                ClassHierarchyResolver.ClassHierarchyInfo info =
                        ClassHierarchyResolver.defaultResolver().getClassInfo(desc);
                return info != null
                        ? info
                        : ClassHierarchyResolver.ClassHierarchyInfo.ofClass(ConstantDescs.CD_Object);
            }));

    /**
     * Builds a class targeting Java 25 (spec 19.1), carrying JSpecify's {@code @NullMarked}.
     *
     * <p>The version is pinned rather than left to {@link ClassFile#of}, which defaults to the
     * JDK running the compiler: the generated code would then track whatever JDK built it, and
     * two developers on different JDKs would emit mutually incompatible artifacts.
     *
     * <p>The marking says that in this class a type saying nothing about null is not null — which is
     * what the generated code already is, since absence is {@code Option} and a failure is a case of
     * the output union (spec 7.3, 12). Saying it is what lets a caller's compiler know: Kotlin reads
     * the annotation off the class file and types what it names as non-null instead of falling back to
     * a platform type, where a null check is neither required nor possible — every member but a record
     * component's accessor, which says it on the return type itself ({@link #CD_NonNull}). It rides
     * on each class rather than on a {@code package-info} because a module's own package is where a
     * consumer's hand-written {@code package-info.java} lives — theirs would be the declaration, and
     * the marking would reach only the modules that own no Java of their own (issue #150). It is read
     * by name, so neither this compiler nor anything downstream needs the JSpecify jar.
     */
    static byte[] build(ClassDesc cd, Consumer<ClassBuilder> handler) {
        return CF.build(cd, cb -> {
            cb.withVersion(ClassFile.JAVA_25_VERSION, 0);
            cb.with(SourceFileAttribute.of(sourceFileName(cd)));
            cb.with(RuntimeVisibleAnnotationsAttribute.of(Annotation.of(CD_NullMarked)));
            handler.accept(cb);
        });
    }

    /**
     * The {@code .sou} source file a generated class came from, for its {@code SourceFile} attribute:
     * the module's simple name plus {@code .sou}. A class's package is its module name (a class is
     * {@code module + "." + name}), so the file name is derived from {@link ClassDesc#packageName()}
     * without threading the original path down. A single-file module named after its file (ADR-0043)
     * makes this exact; a multi-segment module resolves to its last segment.
     */
    private static String sourceFileName(ClassDesc cd) {
        String pkg = cd.packageName();
        if (pkg.isEmpty()) {
            return "source.sou";
        }
        return pkg.substring(pkg.lastIndexOf('.') + 1) + ".sou";
    }

    static final ClassDesc CD_Object = ConstantDescs.CD_Object;
    static final ClassDesc CD_String = ConstantDescs.CD_String;
    static final ClassDesc CD_Long = ClassDesc.of("java.lang.Long");
    static final ClassDesc CD_CharSequence = ClassDesc.of("java.lang.CharSequence");
    static final ClassDesc CD_Map = ClassDesc.of("java.util.Map");
    static final ClassDesc CD_List = ClassDesc.of("java.util.List");
    static final ClassDesc CD_Set = ClassDesc.of("java.util.Set");
    static final ClassDesc CD_LinkedHashMap = ClassDesc.of("java.util.LinkedHashMap");
    static final ClassDesc CD_ArrayList = ClassDesc.of("java.util.ArrayList");
    static final ClassDesc CD_Collection = ClassDesc.of("java.util.Collection");
    static final ClassDesc CD_Result = ClassDesc.of("souther.runtime.Result");
    static final ClassDesc CD_ResultOk = CD_Result.nested("Ok");
    static final ClassDesc CD_ResultErr = CD_Result.nested("Err");
    static final ClassDesc CD_Behavior = ClassDesc.of("souther.runtime.Behavior");
    /** JSpecify's nullness annotation, referenced by name: the jar is on nobody's classpath. */
    static final ClassDesc CD_NullMarked = ClassDesc.of("org.jspecify.annotations.NullMarked");
    /**
     * JSpecify's per-type nullness annotation. {@code @NullMarked} on the class says the same thing
     * for every type in it, and that is what a Kotlin reader acts on — except on a record's component
     * accessors, which Kotlin types from the record component and reaches without applying the
     * marking, so those say it on the return type itself (spec §jvm-nullness).
     */
    static final ClassDesc CD_NonNull = ClassDesc.of("org.jspecify.annotations.NonNull");
    /** The superclass of a data / unit class: they are records (spec 19.2). */
    static final ClassDesc CD_Record = ClassDesc.of("java.lang.Record");
    static final ClassDesc CD_Fn = ClassDesc.of("souther.runtime.Fn");
    static final MethodTypeDesc MTD_Fn_apply =
            MethodTypeDesc.of(ClassDesc.of("java.lang.Object"), ClassDesc.of("java.lang.Object").arrayType());
    static final ClassDesc CD_ConstraintViolation =
            ClassDesc.of("souther.runtime.ConstraintViolation");
    static final ClassDesc CD_UnreachableReached =
            ClassDesc.of("souther.runtime.UnreachableReached");
    /** {@code UnreachableReached.reached(String)}: aborts, typed as answering the position's value. */
    static final MethodTypeDesc MTD_reached = MethodTypeDesc.of(CD_Object, CD_String);
    /** The failure side of {@code __construct}: which clause of which type did not hold. */
    static final ClassDesc CD_InvariantFailure = ClassDesc.of("souther.runtime.InvariantFailure");
    static final MethodTypeDesc MTD_failureOf =
            MethodTypeDesc.of(CD_InvariantFailure, CD_String, CD_String, CD_String);
    static final MethodTypeDesc MTD_failureUnnamed =
            MethodTypeDesc.of(CD_InvariantFailure, CD_String, CD_String);
    /** {@code clause()}: the failing clause's name, or null where it was declared without one. */
    static final MethodTypeDesc MTD_failureClause = MethodTypeDesc.of(CD_String);
    /** {@code meta()}: the rejecting type, and the clause where it has a name. */
    static final MethodTypeDesc MTD_failureMeta = MethodTypeDesc.of(CD_Map);
    static final ClassDesc CD_IntMath = ClassDesc.of("souther.runtime.IntMath");
    /** {@code (long, long) -> long}: overflow-checked Int arithmetic (spec 18.2). */
    static final MethodTypeDesc MTD_intExact =
            MethodTypeDesc.of(ConstantDescs.CD_long, ConstantDescs.CD_long, ConstantDescs.CD_long);
    static final ClassDesc CD_DivisionByZero = ClassDesc.of("souther.runtime.DivisionByZero");
    static final ClassDesc CD_NotANumber = ClassDesc.of("souther.runtime.NotANumber");
    static final ClassDesc CD_Boolean = ClassDesc.of("java.lang.Boolean");
    static final ClassDesc CD_BigDecimal = ClassDesc.of("java.math.BigDecimal");
    static final ClassDesc CD_DecimalMath = ClassDesc.of("souther.runtime.DecimalMath");
    /** {@code BigDecimal add/subtract/multiply(BigDecimal) -> BigDecimal}: the Decimal `+ - *` ops. */
    static final MethodTypeDesc MTD_bdArith = MethodTypeDesc.of(CD_BigDecimal, CD_BigDecimal);
    /** {@code DecimalMath.divide(BigDecimal, BigDecimal) -> BigDecimal}: the Decimal `/` operator. */
    static final MethodTypeDesc MTD_bdDivideOp =
            MethodTypeDesc.of(CD_BigDecimal, CD_BigDecimal, CD_BigDecimal);
    static final ClassDesc CD_RoundingMode = ClassDesc.of("java.math.RoundingMode");
    /** {@code BigDecimal.divide(BigDecimal, int, RoundingMode)} (spec 18.3). */
    static final MethodTypeDesc MTD_bdDivide =
            MethodTypeDesc.of(CD_BigDecimal, CD_BigDecimal, ConstantDescs.CD_int, CD_RoundingMode);
    static final ClassDesc CD_LocalDate = ClassDesc.of("java.time.LocalDate");
    static final ClassDesc CD_LocalDateTime = ClassDesc.of("java.time.LocalDateTime");
    static final ClassDesc CD_Lists = ClassDesc.of("souther.runtime.Lists");
    static final ClassDesc CD_Strings = ClassDesc.of("souther.runtime.Strings");
    static final ClassDesc CD_Maps = ClassDesc.of("souther.runtime.Maps");
    static final ClassDesc CD_Sets = ClassDesc.of("souther.runtime.Sets");
    static final ClassDesc CD_Temporals = ClassDesc.of("souther.runtime.Temporals");
    static final ClassDesc CD_Option = ClassDesc.of("souther.runtime.Option");
    static final ClassDesc CD_Options = ClassDesc.of("souther.runtime.Options");
    static final ClassDesc CD_OptionSome = CD_Option.nested("Some");
    static final ClassDesc CD_OptionNone = CD_Option.nested("None");
    static final ClassDesc CD_IllegalStateException = ClassDesc.of("java.lang.IllegalStateException");

    static final MethodTypeDesc MTD_void = MethodTypeDesc.of(ConstantDescs.CD_void);
    static final MethodTypeDesc MTD_Result_Object = MethodTypeDesc.of(CD_Result, CD_Object);
    static final MethodTypeDesc MTD_Object = MethodTypeDesc.of(CD_Object);
    static final MethodTypeDesc MTD_size = MethodTypeDesc.of(ConstantDescs.CD_int);
    static final MethodTypeDesc MTD_ArrayList_add = MethodTypeDesc.of(ConstantDescs.CD_boolean, CD_Object);
    static final MethodTypeDesc MTD_List_copyOf = MethodTypeDesc.of(CD_List, CD_Collection);
    static final MethodTypeDesc MTD_Lists_concat = MethodTypeDesc.of(CD_List, CD_List, CD_List);
    static final MethodTypeDesc MTD_Lists_append = MethodTypeDesc.of(CD_List, CD_List, CD_Object);
    static final MethodTypeDesc MTD_Lists_sort = MethodTypeDesc.of(CD_List, CD_List);
    static final MethodTypeDesc MTD_Lists_build =
            MethodTypeDesc.of(CD_List, CD_Fn, CD_List, ConstantDescs.CD_long);
    static final MethodTypeDesc MTD_Lists_grow = MethodTypeDesc.of(CD_List, CD_List, CD_Object);
    static final MethodTypeDesc MTD_Lists_growAll = MethodTypeDesc.of(CD_List, CD_List, CD_List);
    static final MethodTypeDesc MTD_Maps_build =
            MethodTypeDesc.of(CD_Map, CD_Fn, CD_List, ConstantDescs.CD_long);
    static final MethodTypeDesc MTD_Maps_put = MethodTypeDesc.of(CD_Map, CD_Map, CD_Object, CD_Object);
    static final MethodTypeDesc MTD_Lists_builder = MethodTypeDesc.of(CD_List);
    static final MethodTypeDesc MTD_Lists_sealed = MethodTypeDesc.of(CD_List, CD_List);
    static final MethodTypeDesc MTD_Maps_builder = MethodTypeDesc.of(CD_Map);
    static final MethodTypeDesc MTD_Maps_sealed = MethodTypeDesc.of(CD_Map, CD_Map);
    static final MethodTypeDesc MTD_next = MethodTypeDesc.of(CD_Object);
    static final MethodTypeDesc MTD_Strings_split = MethodTypeDesc.of(CD_List, CD_String, CD_String);
    static final MethodTypeDesc MTD_Strings_join = MethodTypeDesc.of(CD_String, CD_List, CD_String);
    static final MethodTypeDesc MTD_Strings_replace =
            MethodTypeDesc.of(CD_String, CD_String, CD_String, CD_String);
    static final MethodTypeDesc MTD_Strings_words = MethodTypeDesc.of(CD_List, CD_String);
    static final MethodTypeDesc MTD_Strings_fromInt = MethodTypeDesc.of(CD_String, ConstantDescs.CD_long);
    static final ClassDesc CD_Comparable = ClassDesc.of("java.lang.Comparable");
    static final MethodTypeDesc MTD_compareTo_Object = MethodTypeDesc.of(ConstantDescs.CD_int, CD_Object);
    static final MethodTypeDesc MTD_Map_put = MethodTypeDesc.of(CD_Object, CD_Object, CD_Object);
    static final MethodTypeDesc MTD_apply = MethodTypeDesc.of(CD_Object, CD_Object);
    static final MethodTypeDesc MTD_orThrow = MethodTypeDesc.of(CD_Object, CD_Result);
    static final ClassDesc CD_StringBuilder = ClassDesc.of("java.lang.StringBuilder");
    static final MethodTypeDesc MTD_SB_appendString =
            MethodTypeDesc.of(CD_StringBuilder, CD_String);
    static final MethodTypeDesc MTD_SB_appendObject =
            MethodTypeDesc.of(CD_StringBuilder, CD_Object);
    static final MethodTypeDesc MTD_SB_appendLong =
            MethodTypeDesc.of(CD_StringBuilder, ConstantDescs.CD_long);
    static final MethodTypeDesc MTD_SB_appendBoolean =
            MethodTypeDesc.of(CD_StringBuilder, ConstantDescs.CD_boolean);
    static final MethodTypeDesc MTD_toString = MethodTypeDesc.of(CD_String);
    static final MethodTypeDesc MTD_Long_valueOf = MethodTypeDesc.of(CD_Long, ConstantDescs.CD_long);
    static final MethodTypeDesc MTD_Boolean_valueOf =
            MethodTypeDesc.of(CD_Boolean, ConstantDescs.CD_boolean);

    // --- Raoh 0.6.0 decode/encode targets (generated code depends on Raoh directly; spec 10.6) ---
    static final ClassDesc CD_Class = ClassDesc.of("java.lang.Class");
    static final ClassDesc CD_RDecoder = ClassDesc.of("net.unit8.raoh.decode.Decoder");
    static final ClassDesc CD_REncoder = ClassDesc.of("net.unit8.raoh.encode.Encoder");
    static final ClassDesc CD_RResult = ClassDesc.of("net.unit8.raoh.Result");
    static final ClassDesc CD_ROk = ClassDesc.of("net.unit8.raoh.Ok");
    static final ClassDesc CD_RErr = ClassDesc.of("net.unit8.raoh.Err");
    static final ClassDesc CD_RIssues = ClassDesc.of("net.unit8.raoh.Issues");
    static final ClassDesc CD_RPath = ClassDesc.of("net.unit8.raoh.Path");
    static final ClassDesc CD_ObjectDecoders = ClassDesc.of("net.unit8.raoh.decode.ObjectDecoders");
    static final ClassDesc CD_MapDecoders = ClassDesc.of("net.unit8.raoh.decode.map.MapDecoders");
    static final ClassDesc CD_JsonDecoders = ClassDesc.of("net.unit8.raoh.json.JsonDecoders");
    static final ClassDesc CD_JooqDecoders = ClassDesc.of("net.unit8.raoh.jooq.JooqRecordDecoders");
    static final ClassDesc CD_RDecoders = ClassDesc.of("net.unit8.raoh.decode.Decoders");
    static final ClassDesc CD_RVariant = CD_RDecoders.nested("Variant");
    static final ClassDesc CD_FieldDecoder = ClassDesc.of("net.unit8.raoh.decode.FieldDecoder");
    static final ClassDesc CD_StringDecoder = ClassDesc.of("net.unit8.raoh.decode.builtin.StringDecoder");
    static final ClassDesc CD_LongDecoder = ClassDesc.of("net.unit8.raoh.decode.builtin.LongDecoder");
    static final ClassDesc CD_BoolDecoder = ClassDesc.of("net.unit8.raoh.decode.builtin.BoolDecoder");
    static final ClassDesc CD_DecimalDecoder = ClassDesc.of("net.unit8.raoh.decode.builtin.DecimalDecoder");
    static final ClassDesc CD_TemporalDecoder = ClassDesc.of("net.unit8.raoh.decode.builtin.TemporalDecoder");
    static final ClassDesc CD_ListDecoder = ClassDesc.of("net.unit8.raoh.decode.builtin.ListDecoder");
    static final ClassDesc CD_RecordDecoder = ClassDesc.of("net.unit8.raoh.decode.builtin.RecordDecoder");
    static final ClassDesc CD_ObjectEncoders = ClassDesc.of("net.unit8.raoh.encode.ObjectEncoders");
    static final ClassDesc CD_MapEncoders = ClassDesc.of("net.unit8.raoh.encode.MapEncoders");
    static final ClassDesc CD_MapEncVariant = CD_MapEncoders.nested("Variant");

    // Souther Result stays for the behavior/__construct side (Raoh-free)
    static final MethodTypeDesc MTD_Result_ok = MethodTypeDesc.of(CD_Result, CD_Object);
    static final MethodTypeDesc MTD_Result_err = MethodTypeDesc.of(CD_Result, CD_Object);
    // Raoh decode/encode SAMs, factories, combinators
    static final MethodTypeDesc MTD_Rdecode = MethodTypeDesc.of(CD_RResult, CD_Object, CD_RPath);
    static final MethodTypeDesc MTD_Rencode = MethodTypeDesc.of(CD_Object, CD_Object);
    static final MethodTypeDesc MTD_Rdecoder = MethodTypeDesc.of(CD_RDecoder);
    static final MethodTypeDesc MTD_Rencoder = MethodTypeDesc.of(CD_REncoder);
    static final MethodTypeDesc MTD_leafString = MethodTypeDesc.of(CD_StringDecoder);
    static final MethodTypeDesc MTD_leafLong = MethodTypeDesc.of(CD_LongDecoder);
    static final MethodTypeDesc MTD_leafBool = MethodTypeDesc.of(CD_BoolDecoder);
    static final MethodTypeDesc MTD_leafDecimal = MethodTypeDesc.of(CD_DecimalDecoder);
    static final MethodTypeDesc MTD_leafTemporal = MethodTypeDesc.of(CD_TemporalDecoder);
    static final MethodTypeDesc MTD_field = MethodTypeDesc.of(CD_FieldDecoder, CD_String, CD_RDecoder);
    static final MethodTypeDesc MTD_optionalField = MethodTypeDesc.of(CD_RDecoder, CD_String, CD_RDecoder);
    static final MethodTypeDesc MTD_listDec = MethodTypeDesc.of(CD_ListDecoder, CD_RDecoder);
    static final MethodTypeDesc MTD_mapDec = MethodTypeDesc.of(CD_RecordDecoder, CD_RDecoder);
    static final MethodTypeDesc MTD_Rvariant = MethodTypeDesc.of(CD_RVariant, CD_String, CD_RDecoder);
    static final MethodTypeDesc MTD_Rdiscriminate =
            MethodTypeDesc.of(CD_RDecoder, CD_String, CD_RDecoder, CD_RVariant.arrayType());
    static final MethodTypeDesc MTD_Rok = MethodTypeDesc.of(CD_RResult, CD_Object);
    static final MethodTypeDesc MTD_Rerr = MethodTypeDesc.of(CD_RResult, CD_RIssues);
    static final MethodTypeDesc MTD_Rfail = MethodTypeDesc.of(CD_RResult, CD_RPath, CD_String, CD_String);
    static final MethodTypeDesc MTD_Rencode_leaf = MethodTypeDesc.of(CD_REncoder);
    static final MethodTypeDesc MTD_Rencode_list = MethodTypeDesc.of(CD_REncoder, CD_REncoder);
    static final ClassDesc CD_Function = ClassDesc.of("java.util.function.Function");
    // Newtype-keyed Map codec: decode remaps String keys into the key newtype via
    // flatMapWithPath + a generated $Dec.__rekey helper; encode renders keys bare via Maps.mapKeys.
    static final ClassDesc CD_BiFunction = ClassDesc.of("java.util.function.BiFunction");
    static final ClassDesc CD_Iterator = ClassDesc.of("java.util.Iterator");
    static final ClassDesc CD_MapEntry = CD_Map.nested("Entry");
    static final MethodTypeDesc MTD_flatMapWithPath = MethodTypeDesc.of(CD_RDecoder, CD_BiFunction);
    static final MethodTypeDesc MTD_rekey = MethodTypeDesc.of(CD_RResult, CD_Map, CD_RPath);
    static final MethodTypeDesc MTD_fromName = MethodTypeDesc.of(CD_RResult, CD_String, CD_RPath);
    /** The synthetic {@code static String __tag(Object)} an enumeration's sealed interface carries:
     *  which case a value is, as the name its boundary form uses. */
    static final String TAG_METHOD = "__tag";
    static final MethodTypeDesc MTD_tag = MethodTypeDesc.of(CD_String, CD_Object);
    /** {@code static int __order(Object)} / {@code static Comparator __ordering()}: an enumeration's
     *  declaration order, held by the sum rather than by its case values. */
    static final String ORDER_METHOD = "__order";
    static final String ORDERING_METHOD = "__ordering";
    static final MethodTypeDesc MTD_order = MethodTypeDesc.of(ConstantDescs.CD_int, CD_Object);
    static final ClassDesc CD_Comparator = ClassDesc.of("java.util.Comparator");
    static final ClassDesc CD_ToIntFunction = ClassDesc.of("java.util.function.ToIntFunction");
    static final MethodTypeDesc MTD_ordering = MethodTypeDesc.of(CD_Comparator);
    static final MethodTypeDesc MTD_entrySet = MethodTypeDesc.of(CD_Set);
    static final MethodTypeDesc MTD_iterator = MethodTypeDesc.of(CD_Iterator);
    static final MethodTypeDesc MTD_hasNext = MethodTypeDesc.of(ConstantDescs.CD_boolean);
    static final MethodTypeDesc MTD_getKeyValue = MethodTypeDesc.of(CD_Object);
    static final MethodTypeDesc MTD_Path_append = MethodTypeDesc.of(CD_RPath, CD_String);
    static final MethodTypeDesc MTD_mapKeys = MethodTypeDesc.of(CD_Map, CD_Map, CD_Function);
    static final MethodTypeDesc MTD_mapKeysWith = MethodTypeDesc.of(CD_Map, CD_Function, CD_Map);
    static final MethodTypeDesc MTD_value = MethodTypeDesc.of(CD_String);
    /** {@code Encoder.contramap(Function)}: pre-processes the value an element encoder receives —
     * a nested Set is listed, a nested newtype-keyed Map has its keys rendered bare. */
    static final MethodTypeDesc MTD_Rencoder_contramap = MethodTypeDesc.of(CD_REncoder, CD_Function);
    static final MethodTypeDesc MTD_Sets_toList = MethodTypeDesc.of(CD_List, CD_Set);
    /** {@code Decoder.map(Function)}: turns a {@code Decoder<I, List<T>>} into a {@code Decoder<I, Set<T>>}. */
    static final MethodTypeDesc MTD_Rdecoder_map = MethodTypeDesc.of(CD_RDecoder, CD_Function);
    // A newtype's invariant as Raoh constraints on its leaf decoder (issue #83): the recognised
    // shapes call the typed decoder's own constraint, and what is left calls `refine` with the
    // invariant as a predicate.
    static final ClassDesc CD_Predicate = ClassDesc.of("java.util.function.Predicate");
    static final ClassDesc CD_Pattern = ClassDesc.of("java.util.regex.Pattern");
    static final MethodTypeDesc MTD_patternCompile = MethodTypeDesc.of(CD_Pattern, CD_String);
    static final MethodTypeDesc MTD_strLengthBound = MethodTypeDesc.of(CD_StringDecoder, ConstantDescs.CD_int);
    static final MethodTypeDesc MTD_strPattern = MethodTypeDesc.of(CD_StringDecoder, CD_Pattern);
    static final MethodTypeDesc MTD_longBound = MethodTypeDesc.of(CD_LongDecoder, ConstantDescs.CD_long);
    static final MethodTypeDesc MTD_longSign = MethodTypeDesc.of(CD_LongDecoder);
    static final MethodTypeDesc MTD_decBound = MethodTypeDesc.of(CD_DecimalDecoder, CD_BigDecimal);
    static final MethodTypeDesc MTD_decSign = MethodTypeDesc.of(CD_DecimalDecoder);
    /** A list's element-count bound ({@code minSize}/{@code maxSize}/{@code fixedSize}) and its
     *  argument-free constraints ({@code nonempty}/{@code unique}). */
    static final MethodTypeDesc MTD_listSizeBound =
            MethodTypeDesc.of(CD_ListDecoder, ConstantDescs.CD_int);
    static final MethodTypeDesc MTD_listSign = MethodTypeDesc.of(CD_ListDecoder);
    /** A map's entry-count bound: Raoh decodes a map as a record of its values. */
    static final MethodTypeDesc MTD_recordSizeBound =
            MethodTypeDesc.of(CD_RecordDecoder, ConstantDescs.CD_int);
    /** {@code Decoder.refine(Predicate, BiFunction)}: the failure is built by the caller, so it is a
     *  {@code Result.fail} (resolvable) rather than the {@code failCustom} the message overload makes. */
    static final MethodTypeDesc MTD_Rrefine = MethodTypeDesc.of(CD_RDecoder, CD_Predicate, CD_BiFunction);
    static final MethodTypeDesc MTD_invariantFailure = MethodTypeDesc.of(CD_RResult, CD_Object, CD_RPath);
    /** The same helper with the failing clause's name captured ahead of the two SAM arguments. */
    static final MethodTypeDesc MTD_invariantFailureNamed =
            MethodTypeDesc.of(CD_RResult, CD_String, CD_Object, CD_RPath);
    static final MethodTypeDesc MTD_Rfail4 =
            MethodTypeDesc.of(CD_RResult, CD_RPath, CD_String, CD_String, CD_Map);
    static final MethodTypeDesc MTD_ctfeCheckObject = MethodTypeDesc.of(ConstantDescs.CD_boolean, CD_Object);
    /** {@code LambdaMetafactory.metafactory} — the bootstrap that materialises a method reference as a
     *  functional-interface instance, so {@code Sets::fromList} becomes a {@code Function} for {@code map}. */
    static final DirectMethodHandleDesc BSM_METAFACTORY = MethodHandleDesc.ofMethod(
            DirectMethodHandleDesc.Kind.STATIC,
            ClassDesc.of("java.lang.invoke.LambdaMetafactory"), "metafactory",
            MethodTypeDesc.of(
                    ClassDesc.of("java.lang.invoke.CallSite"),
                    ClassDesc.of("java.lang.invoke.MethodHandles").nested("Lookup"),
                    ClassDesc.of("java.lang.String"),
                    ClassDesc.of("java.lang.invoke.MethodType"),
                    ClassDesc.of("java.lang.invoke.MethodType"),
                    ClassDesc.of("java.lang.invoke.MethodHandle"),
                    ClassDesc.of("java.lang.invoke.MethodType")));
    static final MethodTypeDesc MTD_Rencode_variant =
            MethodTypeDesc.of(CD_MapEncVariant, CD_Class, CD_String, CD_REncoder);
    static final MethodTypeDesc MTD_Rencode_discriminate =
            MethodTypeDesc.of(CD_REncoder, CD_String, CD_MapEncVariant.arrayType());
    static final MethodTypeDesc MTD_Issues_merge = MethodTypeDesc.of(CD_RIssues, CD_RIssues);
    static final MethodTypeDesc MTD_Issues_isEmpty = MethodTypeDesc.of(ConstantDescs.CD_boolean);
    static final MethodTypeDesc MTD_Err_issues = MethodTypeDesc.of(CD_RIssues);
    static final MethodTypeDesc MTD_nested = MethodTypeDesc.of(CD_RDecoder, CD_RDecoder);
    static final ClassDesc CD_JavaOptional = ClassDesc.of("java.util.Optional");
    static final MethodTypeDesc MTD_ofOptional = MethodTypeDesc.of(CD_Option, CD_JavaOptional);
    static final MethodTypeDesc MTD_error = MethodTypeDesc.of(CD_Object);
    // Per-source (JSON / jOOQ) decode targets (spec 10.6). JooqRecordDecoders.field returns a
    // JooqRecordDecoder (not FieldDecoder); JsonDecoders.field returns FieldDecoder like the map source.
    static final ClassDesc CD_JooqRecordDecoder = ClassDesc.of("net.unit8.raoh.jooq.JooqRecordDecoder");
    static final MethodTypeDesc MTD_fieldJooq =
            MethodTypeDesc.of(CD_JooqRecordDecoder, CD_String, CD_RDecoder);
    static final MethodTypeDesc MTD_optFieldJooq =
            MethodTypeDesc.of(CD_JooqRecordDecoder, CD_String, CD_RDecoder);

    // Value-equality / hashCode targets, shared by the value-class equality codegen and the `==`
    // match arm (a Decimal compares by value, a reference through Objects.equals).
    static final ClassDesc CD_Objects = ClassDesc.of("java.util.Objects");
    static final MethodTypeDesc MTD_BD_compareTo =
            MethodTypeDesc.of(ConstantDescs.CD_int, CD_BigDecimal);
    static final MethodTypeDesc MTD_BD_strip = MethodTypeDesc.of(CD_BigDecimal);
    static final MethodTypeDesc MTD_Objects_equals =
            MethodTypeDesc.of(ConstantDescs.CD_boolean, CD_Object, CD_Object);
    /** {@code Object.equals(Object)} — a constant receiver compares against a value that may be null. */
    static final MethodTypeDesc MTD_equalsObject =
            MethodTypeDesc.of(ConstantDescs.CD_boolean, CD_Object);
    static final MethodTypeDesc MTD_Objects_hashCode =
            MethodTypeDesc.of(ConstantDescs.CD_int, CD_Object);
    static final MethodTypeDesc MTD_Long_hashCode =
            MethodTypeDesc.of(ConstantDescs.CD_int, ConstantDescs.CD_long);
}
