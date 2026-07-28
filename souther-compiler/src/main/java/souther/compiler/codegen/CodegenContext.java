package souther.compiler.codegen;

import souther.compiler.check.Symbols;
import souther.compiler.ast.Ast;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.check.TypeOps;

import java.lang.classfile.ClassFile;
import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static souther.compiler.codegen.Descriptors.*;

/**
 * The module-wide state every generator shares: the symbol table and package map, the name
 * resolution built on them (a type or behavior name to its {@link ClassDesc}), and the sink for the
 * synthetic {@code Fn} classes escaping lambdas compile to. It resolves names and types; it never
 * touches a {@code CodeBuilder}. One instance is built per module in {@link Backend#generate} and
 * handed to {@link Backend.Gen}, and later to the codec and value-class generators.
 */
final class CodegenContext {

    final String pkg;
    final Symbols symbols;
    final Map<String, List<String>> caseToSums;
    final Map<String, String> typePackage;
    /** True when the module has no {@code exposing} clause: everything stays public. */
    final boolean exposeAll;
    /** Base names the module exposes (only these are public when {@link #exposeAll} is false). */
    final Set<String> exposed;
    /** The module's recursive helpers, lowered to static methods on {@code $Fns} (spec 13.1), keyed
     * by helper name. A call to one is an {@code invokestatic}, not an inlined body. */
    final Map<String, Ast.FnDef> recursiveHelpers;

    /** Synthetic {@code Fn} classes generated for escaping lambdas (spec §blocks), merged into the
     * module output once every behavior is generated. */
    private final Map<String, byte[]> synthClasses = new LinkedHashMap<>();
    private int lambdaCounter = 0;

    /** Per-injected-behavior input/success types, set once the module's required behaviors are known
     * ({@link Backend#generate}). Drives the unary-vs-standalone dispatch (issue #57): a required
     * behavior that does not take exactly one input is stored by its own base class and called with
     * {@code invokevirtual}, not the unary {@code Behavior}. Both {@link Backend} and
     * {@link Backend.Gen}/{@code BodyGen} read this, so the field type, ctor param and call
     * descriptor cannot drift apart. */
    private Map<String, List<Type>> reqParams = Map.of();
    private Map<String, Type> reqSuccess = Map.of();

    void setRequiredSignatures(Map<String, List<Type>> params, Map<String, Type> success) {
        this.reqParams = params;
        this.reqSuccess = success;
    }

    /** A required (injected) behavior takes other than one input, so it is a standalone base rather
     * than the unary {@code Behavior} (issue #57, spec §java-base-class). Two inputs are too many to
     * hand along an arrow and none is too few, so both are called on their own class with a typed
     * {@code apply}; only a single input is the transformation {@code Behavior} describes. */
    boolean isStandaloneRequired(String name) {
        List<Type> params = reqParams.get(name);
        return params != null && params.size() != 1;   // absent: not a required behavior at all
    }

    /** The JVM type a required behavior is stored/injected as: its own base class unless it takes
     * exactly one input, which is the unary {@code Behavior} composition contract. */
    ClassDesc requiredFieldType(String name) {
        return isStandaloneRequired(name) ? cdBehavior(name) : CD_Behavior;
    }

    /** The typed {@code apply(A,B,…)} descriptor of a standalone required behavior's base — the same
     * descriptor {@link Backend#generateRequiredBase} declared, so an {@code invokevirtual} on it links. */
    MethodTypeDesc requiredApplyDesc(String name) {
        return typedApplyDesc(name, reqParams.get(name), reqSuccess.get(name));
    }

    /** The interface-facing apply descriptor for a multi-input behavior: each param and the return
     * mapped to its runtime reference type. A collection keeps its {@code java.util.List/Map/Set} (or
     * runtime {@code Option}) interface — not degraded to {@code Object} — with the element type
     * carried by {@link #applySignatureOrNull} (issue #57). */
    MethodTypeDesc typedApplyDesc(String name, List<Type> paramTypes, Type retType) {
        ClassDesc[] p = new ClassDesc[paramTypes.size()];
        for (int i = 0; i < p.length; i++) {
            p[i] = applyParamType(paramTypes.get(i), name);
        }
        return MethodTypeDesc.of(applyParamType(retType, name), p);
    }

    /** The JVM reference type an {@code apply} slot takes for {@code t}: a collection keeps its raw
     * runtime interface ({@code java.util.List/Map/Set}, runtime {@code Option}); a data/union/primitive
     * maps to its ref; anything erased (type var, tuple, fn) falls back to {@code Object}. */
    ClassDesc applyParamType(Type t, String name) {
        if (t instanceof Type.ListOf || t instanceof Type.MapOf
                || t instanceof Type.SetOf || t instanceof Type.OptionOf) {
            return JvmTypes.jvmType(t, this);
        }
        ClassDesc r = refTypeOrNull(t, name);
        return r != null ? r : CD_Object;
    }

    /** A generic {@code Signature} for a typed {@code apply}, or null when no param/return is a
     * collection (the raw descriptor then already names every type). Mirrors the data-factory signature:
     * a collection element is carried via {@link JvmTypes#genericSig}, everything else by its descriptor. */
    String applySignatureOrNull(String name, List<Type> params, Type ret) {
        boolean anyContainer = JvmTypes.genericSig(ret, this) != null;
        for (Type p : params) {
            anyContainer |= JvmTypes.genericSig(p, this) != null;
        }
        if (!anyContainer) {
            return null;
        }
        StringBuilder sb = new StringBuilder("(");
        for (Type p : params) {
            sb.append(applySigElem(p, name));
        }
        return sb.append(")").append(applySigElem(ret, name)).toString();
    }

    private String applySigElem(Type t, String name) {
        String g = JvmTypes.genericSig(t, this);
        return g != null ? g : applyParamType(t, name).descriptorString();
    }

    /** The signature-form of a single {@code Behavior<In, Out>} type argument: a collection carries its
     * element type; a data/primitive/union its descriptor; a truly erased type (var/tuple/fn) yields
     * null, which suppresses the whole generic {@code Behavior} signature. */
    String sigRefOrNull(Type t, String name) {
        String g = JvmTypes.genericSig(t, this);
        if (g != null) {
            return g;
        }
        ClassDesc r = refTypeOrNull(t, name);
        return r != null ? r.descriptorString() : null;
    }

    CodegenContext(String pkg, Symbols symbols, Map<String, List<String>> caseToSums,
                   Map<String, String> typePackage, boolean exposeAll, Set<String> exposed,
                   Map<String, Ast.FnDef> recursiveHelpers) {
        this.pkg = pkg;
        this.symbols = symbols;
        this.caseToSums = caseToSums;
        this.typePackage = typePackage;
        this.exposeAll = exposeAll;
        this.exposed = exposed;
        this.recursiveHelpers = recursiveHelpers;
    }

    /** {@code ACC_PUBLIC} when the name is exposed (or the module exposes all), else 0. */
    int pub(String name) {
        return (exposeAll || exposed.contains(name)) ? ClassFile.ACC_PUBLIC : 0;
    }

    // The same handful of names is turned into a descriptor again at every emission site, and
    // ClassDesc.of re-validates the name on each call, so each map keeps what it has already built.
    // They live on the context, so they are per module generated and never outlive it.
    private final Map<String, ClassDesc> typeDescs = new HashMap<>();
    private final Map<String, ClassDesc> behaviorDescs = new HashMap<>();
    private final Map<String, ClassDesc> behaviorImplDescs = new HashMap<>();

    /** The class of a type, from the module that declares it — nothing to look up, since a
     * {@link TypeName} already says where it lives. */
    ClassDesc cd(TypeName name) {
        return typeDescs.computeIfAbsent(name.qualified(), ClassDesc::of);
    }

    /**
     * The class of a name as the source (or a derived codec) wrote it. It is resolved the same way
     * the checker resolved it, so an imported type lands in its own package. A name nothing declares
     * is one this backend made up — a generated {@code $Enc}/{@code Result} class — and belongs to
     * the module being generated.
     */
    ClassDesc cd(String typeName) {
        return typeDescs.computeIfAbsent(typeName, n -> {
            TypeName resolved = symbols.resolve(n);
            return ClassDesc.of(resolved != null ? resolved.qualified() : pkg + "." + n);
        });
    }

    ClassDesc cdBehavior(String name) {
        return behaviorDescs.computeIfAbsent(name,
                n -> ClassDesc.of(typePackage.getOrDefault(n, pkg) + "." + behaviorClass(n)));
    }

    /** The implementation class behind a fn/pipe behavior's public interface: {@code <名>$Impl}.
     * The interface (named {@link #behaviorClass}) is what Java code declares; the {@code $Impl}
     * holds the fields, constructor and {@code apply}, and is what a pipeline instantiates. Injected
     * behaviors have no {@code $Impl} (their abstract base is the named class). */
    ClassDesc cdBehaviorImpl(String name) {
        return behaviorImplDescs.computeIfAbsent(name,
                n -> ClassDesc.of(typePackage.getOrDefault(n, pkg) + "." + behaviorImplClass(n)));
    }

    /**
     * The generated class simple-name for a behavior: its name with the first letter capitalized
     * (spec 19.5). A Japanese leading character has no upper-case form, so a Japanese-named behavior
     * is emitted unchanged. The behavior's name stays lower-case wherever it is an identity — an
     * injected field name, a requirement-set entry, a signature-map key — and only the emitted class
     * name is capitalized.
     */
    static String behaviorClass(String name) {
        if (name.isEmpty()) {
            return name;
        }
        return Character.toUpperCase(name.charAt(0)) + name.substring(1);
    }

    /** The {@code $Impl} simple-name for a fn/pipe behavior (see {@link #cdBehaviorImpl}). */
    static String behaviorImplClass(String name) {
        return behaviorClass(name) + "$Impl";
    }

    /** The {@code $Fns} method name for a recursive helper. A module-own helper keeps its bare name;
     * a prelude recursive helper reached under a qualified name ({@code List.foldFrom}) has the dot
     * mangled to {@code $}, since a JVM method name cannot contain a dot. */
    static String recursiveHelperMethod(String name) {
        return name.replace('.', '$');
    }

    /** The generated result-union simple-name for a behavior with an anonymous-union output
     * (spec 19.8): {@code <名>Result}. Only the union case gets one; a named-sum or single-case
     * output uses that type directly. */
    static String behaviorResultClass(String name) {
        return behaviorClass(name) + "Result";
    }

    /** The JVM class of an output case. The built-in {@code DivisionByZero}/{@code NotANumber} need
     * no special case: their {@link TypeName} names {@code souther.runtime}, which is where they are.
     * An invariant violation is no longer a case — it aborts (spec 7.3, 9.4) — so there is no
     * 制約違反 case here. */
    ClassDesc caseClass(TypeName typeName) {
        return cd(typeName);
    }

    /** The class a match case is tested against: a boxed/reference class for a primitive case,
     * otherwise the case's data class, which its resolved name already names. */
    ClassDesc matchCaseClass(TypeName caseName) {
        if (!caseName.isPrimitive()) {
            return caseClass(caseName);
        }
        return switch (caseName.name()) {
            case "Int" -> CD_Long;
            case "Bool" -> CD_Boolean;
            case "Decimal" -> CD_BigDecimal;
            case "String" -> CD_String;
            case "Date" -> CD_LocalDate;
            case "DateTime" -> CD_LocalDateTime;
            // Option's `Some`/`None` are named here as well, being declared by no module, and never
            // reach this: an Option match dispatches on the runtime Option classes, not on an arm's
            // own name. Anything else naming no class is a resolution that should not have happened.
            default -> throw new IllegalStateException("no class for the case " + caseName);
        };
    }

    ClassDesc[] caseInterfaces(String name) {
        List<ClassDesc> ifaces = new ArrayList<>();
        for (String sum : caseToSums.getOrDefault(name, List.of())) {
            ifaces.add(cd(sum));
        }
        return ifaces.toArray(new ClassDesc[0]);
    }

    /**
     * The single reference class a behavior's input or output success type maps to, for a generic
     * {@code Behavior<In, Out>} signature: the {@code <名>Result} interface for an anonymous union, the
     * named data/sum for a single case, the boxed class for a primitive. Returns {@code null} for a
     * list/option/map, which has no single reference class to name here.
     */
    ClassDesc refTypeOrNull(Type t, String behaviorName) {
        if (t instanceof Type.Union) {
            return cd(behaviorResultClass(behaviorName));
        }
        if (t instanceof Type.Ref r) {
            return cd(r.name());
        }
        return JvmTypes.boxedPrim(t);
    }

    Map<String, Type> fieldTypes(Ast.Data data) {
        return TypeOps.fieldTypes(data, symbols);
    }

    Type successType(Ast.RetType ret) {
        return TypeOps.successType(ret, symbols);
    }

    /** Whether {@code name} is an imported type or behavior (declared in another module, spec 4). */
    boolean isImported(String name) {
        return typePackage.containsKey(name);
    }

    // --- synthetic-class sink ---

    /** The next id for an escaping lambda's generated {@code $Fn} class (spec §blocks). */
    int nextLambdaId() {
        return lambdaCounter++;
    }

    void addSynth(String className, byte[] bytes) {
        synthClasses.put(className, bytes);
    }

    /** The synthetic classes accumulated so far, for merging into the module output. */
    Map<String, byte[]> synthClasses() {
        return synthClasses;
    }
}
