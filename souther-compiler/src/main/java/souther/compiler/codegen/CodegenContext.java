package souther.compiler.codegen;

import souther.compiler.check.ExpandedClauseLookup;
import souther.compiler.check.InvariantStatements;
import souther.compiler.check.AtomSpace;
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.core.Kernel;
import souther.compiler.core.KernelSignature;
import souther.compiler.core.KernelSignatures;
import souther.compiler.core.ValueShape;
import souther.compiler.check.DerivedSymbols;
import souther.compiler.check.DeclarationKinds;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.PublishedDeclarations;
import souther.compiler.ast.Hir;
import souther.compiler.diag.PhysicalPos;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.check.TypeOps;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.LinkageProjection;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.ValueName;

import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeBuilder;
import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Objects;
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
    final DerivedSymbols symbols;
    /** What the declarations an emitted class names say about themselves. Beside {@link #symbols}
     *  and not read off it, for the reason {@code PublishedDeclarations} gives. */
    final PublishedDeclarations published;

    /** Which form each declaration was written in, for the emissions that only have to tell a sum
     *  from anything else. */
    final DeclarationKinds kinds;

    /** What each declaration that wears one value wraps, for the readings that go through the
     *  name. */
    final NewtypeInners inners;

    /**
     * What the language declares of its kernels: what each takes and answers, as the compilation
     * that checked these bodies settled it.
     *
     * <p>Handed in rather than fetched. A backend that could reach the library would be a backend
     * that could ask it anything, and what it has business asking is what the operation it is
     * emitting a call to was declared with — which is a decision of the language, already made and
     * already carried. Given the value, there is no arrangement under which this emits against one
     * reading and the program says another.
     */
    private final KernelSignatures kernels;

    /** What {@code kernel} was declared to take and answer. */
    KernelSignature kernelSignature(Kernel kernel) {
        return kernels.signatureOf(kernel);
    }
    final Map<String, List<GeneratedClass>> caseToSums;
    final Map<String, String> typePackage;
    /** True when the module has no {@code exposing} clause: everything stays public. */
    final boolean exposeAll;
    /** Base names the module exposes (only these are public when {@link #exposeAll} is false). */
    final Set<String> exposed;
    /**
     * What a call this module leaves standing is typed against, by the name it is reached by.
     *
     * <p>The same answer the check typed those calls against, handed over rather than worked out
     * again. The emitter re-types the expressions it emits — a clause, a rule — and a table built
     * here out of what this module happens to emit would answer for the methods written rather than
     * for the names a call can hold, which is a narrower question and not the one being asked.
     */
    final Map<String, Type> standingCalls;

    /**
     * The texts this module's code was read from, for the debug table.
     *
     * <p>Handed in for the run and not asked for. What line an instruction's code is at is what its
     * file is laid out as at the moment, and a backend that could go and find that out would be a
     * backend that reads the workspace; what it has business knowing is the texts the compilation
     * it is emitting for was given.
     */
    private final SourceLayouts layouts;

    /**
     * Which text the classes generated here are of.
     *
     * <p>A class carries one {@code SourceFile}, and it is this module's. So this is the one text
     * whose line numbers a class generated here can be read against: a place in any other text has
     * no line to contribute, because whatever line that place is at is a line of a file the class
     * does not name, and the file it does name may be shorter than it.
     */
    private final QuotedFrom home;

    /** Where a place sits in the text this module's classes name, or null where it sits in another
     *  text or this compilation holds none. */
    PhysicalPos sits(SourcePos place) {
        if (place == null || !home.equals(place.quotedFrom())) {
            return null;
        }
        return layouts.resolve(place);
    }

    /** Synthetic {@code Fn} classes generated for escaping lambdas (spec §blocks), merged into the
     * module output once every behavior is generated. */
    private final Map<GeneratedClass, byte[]> synthClasses = new LinkedHashMap<>();
    private int lambdaCounter = 0;

    /**
     * Where what a behavior, a declared type or a published value offers on the JVM is read, and
     * where reading another module's is recorded.
     *
     * <p>How a behavior is held, applied and built is read off its projection and nowhere else —
     * this module's own as much as another's, so the field a class holds a behavior in, the
     * constructor that fills it and every call on it are one answer. The declarations this module's
     * code reads through {@link #symbols}, {@link #published}, {@link #kinds} and {@link #inners}
     * are recorded through the same reader, which those were built reading into.
     */
    private final LinkageReader linkage;

    /** What {@code behavior} offers: how it is held, applied and built. */
    LinkageProjection.Behavior behavior(ValueName.Behavior behavior) {
        return linkage.behavior(behavior);
    }

    /** What the declared type at {@code key} offers: its form, its class, what a read finds. */
    LinkageProjection.Data declaredType(TypeKey key) {
        return linkage.data(key);
    }

    /**
     * The entry a product or a newtype is built through: its {@code __construct}, as what the type
     * offers says. Read where any class calls it — its own module's included — and where its own
     * class declares it, so the call and the method are one answer.
     */
    LinkageProjection.Invocation construction(TypeSymbol.AtModule type) {
        return declaredType(type.key()).construction().orElseThrow(() ->
                new IllegalStateException("`" + type + "` is built through an entry and offers"
                        + " none"));
    }

    /** Emits the instruction {@code invocation} describes. */
    static void invoke(CodeBuilder code, LinkageProjection.Invocation invocation) {
        switch (invocation.opcode()) {
            case STATIC -> code.invokestatic(invocation.ownerClass(), invocation.method(),
                    invocation.methodType());
            case VIRTUAL -> code.invokevirtual(invocation.ownerClass(), invocation.method(),
                    invocation.methodType());
            case INTERFACE -> code.invokeinterface(invocation.ownerClass(), invocation.method(),
                    invocation.methodType());
        }
    }

    /** What the published value {@code value} offers: its entry, and what it answers. */
    LinkageProjection.Value publishedValue(ValueName.Helper value) {
        return linkage.value(value);
    }

    /**
     * This module's declarations' invariant clauses in the representation the language's own operations
     * survive in ({@link souther.compiler.check.InliningPolicy#DISCHARGE}). The constraint mapping a
     * derived decoder does is written against those operations, so it reads this rather than the
     * settled form the rest of the backend emits from.
     *
     * <p>Null until it is set, and not an empty one. A module reading as stating nothing and a module
     * whose representation never arrived are the same empty map and opposite facts, and a decoder
     * built from the second would silently constrain nothing.
     */
    private ExpandedClauseLookup dischargeInvariants;

    /**
     * Where each behavior's declared relation is checked, as it was decided before emission.
     *
     * <p>Set rather than worked out, for the reason it is a decision and not a pair of facts: the
     * emitter is adding to a set of injected names while it runs, so a reader here would be reading
     * that set at whatever point it happened to be at.
     */
    private Map<ValueName.Behavior, EnsuresEnforcement> ensuresChecks = Map.of();

    void setEnsuresChecks(Map<ValueName.Behavior, EnsuresEnforcement> checks) {
        this.ensuresChecks = Map.copyOf(checks);
    }

    /**
     * What is being done about {@code behavior}'s clause.
     *
     * <p>{@link EnsuresEnforcement.NotDecidedHere} for a behavior another module declared, which the
     * lookup answers rather than this: a table of this compilation's decisions holds one for every
     * behavior it declares, so a name it has nothing under is a name from somewhere else — which is
     * not the same answer as having decided there is no check.
     */
    EnsuresEnforcement ensuresCheckOf(ValueName.Behavior behavior) {
        return EnsuresEnforcement.in(ensuresChecks, pkg, behavior);
    }

    /**
     * What each conjunct of this module's declarations states, statement by statement.
     *
     * <p>The reading the front end made, handed over rather than repeated. What a rule states is
     * settled where the clause's shape was read — a binding crossed, a denial spent — and a backend
     * that read the tree for itself would recognise a rule written out and decline the same rule
     * named through a helper, which is a difference in what a decoder reports and not in the model.
     *
     * <p>Null until it is set, for the reason {@link #dischargeInvariants} gives.
     */
    private InvariantStatements invariantStatements;

    void setInvariantStatements(InvariantStatements statements) {
        this.invariantStatements = statements;
    }

    InvariantStatements invariantStatements() {
        if (invariantStatements == null) {
            throw new IllegalStateException(
                    "what " + pkg + "'s clauses state was never handed over");
        }
        return invariantStatements;
    }

    void setDischargeInvariants(ExpandedClauseLookup clauses) {
        this.dischargeInvariants = clauses;
    }

    ExpandedClauseLookup dischargeInvariants() {
        if (dischargeInvariants == null) {
            throw new IllegalStateException(
                    "the analysis representation of " + pkg + "'s clauses was never handed over");
        }
        return dischargeInvariants;
    }

    private Map<TypeSymbol.AtModule, ValueShape> shapes = Map.of();

    void setValueShapes(Map<TypeSymbol.AtModule, ValueShape> shapes) {
        this.shapes = shapes;
    }

    /**
     * What a value of {@code named} is made of and what must hold of one, as the check answered it.
     *
     * <p>The fields and the clauses together, because binding a field and running a clause are two
     * halves of one environment. Null for a data no module here declares — nothing asks, since a
     * value class is emitted where its type is declared.
     */
    ValueShape shapeOf(TypeSymbol.AtModule named) {
        return shapes.get(named);
    }

    /**
     * The arms to record, where this generation is one that measures. Empty otherwise, which is every
     * generation whose classes are meant to be shipped.
     *
     * <p>Keyed by the identity of the nodes being emitted, so what is set here has to be the plan made
     * from <em>these</em> bodies. Core nodes are records: a plan made from an equal body would answer
     * for the wrong arm and never say so.
     */
    private souther.compiler.coverage.CoverageSites.Plan coverage =
            souther.compiler.coverage.CoverageSites.Plan.NONE;

    void setCoveragePlan(souther.compiler.coverage.CoverageSites.Plan plan) {
        this.coverage = plan;
    }

    boolean measuring() {
        return !coverage.hasNoProbes();
    }

    /**
     * Whether this generation counts what the code goes through.
     *
     * <p>A separate question from {@link #measuring}, and it has to stay separate. Coverage is asked
     * for by a measurement and is about one module's arms; a budget is what every evaluation is held
     * to and covers every module a row reaches. A generation may do either, both, or neither, and the
     * two are planned differently — an arm is a numbered node of a body the plan was made from, while
     * a counted point is any loop the emitter emits, including ones in a decoder that no body has a
     * node for.
     */
    private boolean counting;

    void setCounting(boolean counting) {
        this.counting = counting;
    }

    boolean counting() {
        return counting;
    }

    /**
     * One counted point, where this generation counts them.
     *
     * <p>Every loop the emitter emits goes through here, so a loop added later cannot be a loop that
     * nothing counts. Put on the branch that goes back rather than at the loop's entry: what is being
     * counted is going round again, and a loop that runs no iterations should cost nothing.
     *
     * <p>Emits nothing at all for a generation whose classes ship, so a jar carries no reference to
     * the compiler.
     */
    void countOneStep(java.lang.classfile.CodeBuilder code) {
        if (counting) {
            code.invokestatic(Descriptors.CD_EvaluationContext, "tick",
                    Descriptors.MTD_EvaluationContext_count);
        }
    }

    /**
     * The arm numbers of one node, in the order the emitter emits them.
     *
     * <p>Throws where a measuring generation meets a node the plan does not know. Only bodies the plan
     * was made from ask this, so a node it does not hold is a plan made from other nodes than these —
     * and going on would leave an arm that ran reported as one no row reaches, which reads as a gap in
     * the model rather than as a fault in the measurement.
     */
    int[] probesOf(souther.compiler.core.Core node) {
        int[] arms = coverage.probesOf(node);
        if (arms == null) {
            throw new IllegalStateException("no probe was planned for a "
                    + node.getClass().getSimpleName() + " at " + node.pos()
                    + "; the plan was made from other nodes than these");
        }
        return arms;
    }

    /**
     * Where this comparison's value is recorded, or empty where it is not one of a guard's condition.
     *
     * <p>Not the loud lookup {@link #probesOf} is. An arm the plan does not hold is a plan made from
     * other nodes; a comparison it does not hold is any comparison written outside a condition, which
     * is most of them.
     */
    java.util.Optional<souther.compiler.coverage.ComparisonEmissionSite> comparisonSiteOf(
            souther.compiler.core.Core comparison) {
        // Which comparison the node is, then where a run through it is written down: the catalog
        // answers the first for every comparison the bodies hold, and the plan the second for the
        // ones it instruments. The emitter is walking the tree, so the node is how it gets in.
        return coverage.comparisons().occurrenceAt(comparison)
                .flatMap(coverage::emissionSiteOf);
    }

    /** Records that one planned arm was emitted. */
    void emitted(int site) {
        emittedSites.add(site);
    }

    private final Set<Integer> emittedSites = new java.util.LinkedHashSet<>();

    /**
     * Which planned arms never reached the bytecode.
     *
     * <p>What makes an omission loud. A body the emitter walks without counting its arms — a path
     * nobody thought to say either way about — takes the arms of that behavior out of the measurement
     * silently, and every one of them is then reported as an arm no row goes through.
     */
    List<Integer> plannedButNotEmitted() {
        List<Integer> missing = new java.util.ArrayList<>();
        for (souther.compiler.coverage.CoverageSites.Site site : coverage.sites()) {
            // By the number, because what was emitted is what was written into the code: this is
            // the side of the boundary where a place is a constant in a call, and both families
            // are written the same way there.
            if (!emittedSites.contains(site.index().raw())) {
                missing.add(site.index().raw());
            }
        }
        return missing;
    }

    /** The module being generated. Module is package (spec §modules), so this is also {@link #pkg}. */
    String module() {
        return pkg;
    }

    /** The JVM type a behavior is held as, in a field and as a constructor parameter. */
    ClassDesc requiredFieldType(ValueName.Behavior name) {
        return behavior(name).heldAsClass();
    }

    /** The typed {@code apply} descriptor of one of this module's behaviors, by the rule its
     * projection is made by ({@link BehaviorAbi#typedApply}). A collection keeps its
     * {@code java.util.List/Map/Set} (or runtime {@code Option}) interface — not degraded to
     * {@code Object} — with the element type carried by {@link #applySignatureOrNull}. */
    MethodTypeDesc typedApplyDesc(ValueName.Behavior name, List<Type> paramTypes, Type retType) {
        return BehaviorAbi.typedApply(paramTypes, retType, cdBehaviorResult(name), this::caseClass);
    }

    /** The JVM reference type an {@code apply} slot takes for {@code t} ({@link
     * BehaviorAbi#applyParamType}). */
    ClassDesc applyParamType(Type t, ValueName.Behavior name) {
        return BehaviorAbi.applyParamType(t, cdBehaviorResult(name), this::caseClass);
    }

    /** A generic {@code Signature} for a typed {@code apply}, or null when no param/return is a
     * collection (the raw descriptor then already names every type). Mirrors the data-factory signature:
     * a collection element is carried via {@link JvmTypes#genericSig}, everything else by its descriptor. */
    String applySignatureOrNull(ValueName.Behavior name, List<Type> params, Type ret) {
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

    private String applySigElem(Type t, ValueName.Behavior name) {
        String g = JvmTypes.genericSig(t, this);
        return g != null ? g : applyParamType(t, name).descriptorString();
    }

    /** The signature-form of a single {@code Behavior<In, Out>} type argument: a collection carries its
     * element type; a data/primitive/union its descriptor; a truly erased type (var/tuple/fn) yields
     * null, which suppresses the whole generic {@code Behavior} signature. */
    String sigRefOrNull(Type t, ValueName.Behavior name) {
        String g = JvmTypes.genericSig(t, this);
        if (g != null) {
            return g;
        }
        ClassDesc r = refTypeOrNull(t, name);
        return r != null ? r.descriptorString() : null;
    }

    CodegenContext(String pkg, DerivedSymbols symbols, PublishedDeclarations published,
                   DeclarationKinds kinds,
                   NewtypeInners inners,
                   KernelSignatures kernels,
                   Map<String, List<GeneratedClass>> caseToSums,
                   Map<String, String> typePackage, boolean exposeAll, Set<String> exposed,
                   Map<String, Type> standingCalls, SourceLayouts layouts, QuotedFrom home,
                   LinkageReader linkage) {
        this.linkage = Objects.requireNonNull(linkage,
                "what a module's classes are built against is read through one place");
        this.layouts = layouts;
        this.home = Objects.requireNonNull(home, "the classes of a module are of the text it was read from");
        this.pkg = pkg;
        this.symbols = symbols;
        this.published = published;
        this.kinds = kinds;
        this.inners = inners;
        this.kernels = kernels;
        this.caseToSums = caseToSums;
        this.typePackage = typePackage;
        this.exposeAll = exposeAll;
        this.exposed = exposed;
        this.standingCalls = standingCalls;
    }

    /** {@code ACC_PUBLIC} when the name is exposed (or the module exposes all), else 0. */
    int pub(String name) {
        return (exposeAll || exposed.contains(name)) ? ClassFile.ACC_PUBLIC : 0;
    }

    // The same handful of classes is turned into a descriptor again at every emission site, and
    // ClassDesc.of re-validates the name on each call, so this keeps what it has already built. It
    // lives on the context, so it is per module generated and never outlives it.
    private final Map<GeneratedClass, ClassDesc> descs = new HashMap<>();

    /** The descriptor of a generated class. What it is called is {@link SoutherJvmAbi}'s to say; this
     * only remembers the answer. A class of another module's declaration named here is a class this
     * module is built against, and is recorded as that declaration. */
    ClassDesc cd(GeneratedClass generated) {
        // Asked when a class is first named and not at each reference to it: the answer does not
        // change, and a reference to a class of another module reads that module's exposing.
        return descs.computeIfAbsent(generated, g -> {
            linkage.named(g);
            if (g instanceof GeneratedClass.Value value
                    && value.type() instanceof TypeSymbol.AtModule declared
                    && !symbols.scope().isExposed(declared)) {
                throw new AClassEmittedHereIsOneAnotherModuleKeepsToItself(declared);
            }
            return SoutherJvmAbi.nameOf(g).classDesc();
        });
    }

    /**
     * The code being emitted names the class of a type its own module does not expose.
     *
     * <p>Such a class is package-private, so the JVM refuses the reference when the code runs. What
     * a module publishes is held to this where it is published (E1628), and a module that imports
     * one refused there is not emitted, so a compiler that gets here has emitted a reference that
     * check did not know to ask about. It is a fault of this compiler and no author's to fix, so it
     * is not a diagnostic.
     */
    static final class AClassEmittedHereIsOneAnotherModuleKeepsToItself
            extends IllegalStateException {

        private static final long serialVersionUID = 1L;

        AClassEmittedHereIsOneAnotherModuleKeepsToItself(TypeSymbol type) {
            super("the class of `" + type + "` is emitted into a module that cannot reach it");
        }
    }

    /** The class of a type, from the module that declares it — nothing to look up, since a
     * {@link TypeSymbol} already says where it lives. */
    ClassDesc cd(TypeSymbol name) {
        return cd(new GeneratedClass.Value(name));
    }

    /** The class of a declaration of the module being generated. */
    ClassDesc cd(Hir.Def def) {
        return cd(def.declares());
    }

    ClassDesc cdBehavior(ValueName.Behavior name) {
        return cd(new GeneratedClass.BehaviorInterface(name.module(), name.name()));
    }

    /** The implementation class behind a fn/pipe behavior's public interface. The interface is what
     * Java code declares; the implementation holds the fields, constructor and {@code apply}, and is
     * what a pipeline instantiates. Injected behaviors have none (their abstract base is the named
     * class). */
    ClassDesc cdBehaviorImpl(ValueName.Behavior name) {
        return cd(new GeneratedClass.BehaviorImpl(name.module(), name.name()));
    }

    /**
     * The result-union class of a behavior, in the module that declared the behavior. Nothing declares
     * this class — the backend makes it up — so placing it in the module being generated would be
     * right only for a behavior declared here. An imported one is called on a typed {@code apply}
     * naming this class, and the class lives where the behavior does.
     */
    ClassDesc cdBehaviorResult(ValueName.Behavior name) {
        return cd(new GeneratedClass.BehaviorResult(name.module(), name.name()));
    }

    /**
     * The bridge case a non-local union member reaches its result unions through, in the module that
     * declares the union. A member this module declared implements the union itself; a primitive or
     * a type another module emitted cannot be given that interface, so this module emits a record
     * holding the value and implementing the union in its stead. One per member per module: it
     * carries every result union of this module the member belongs to, which is the rule a local case
     * class already follows (spec §jvm-anonymous-union).
     */
    ClassDesc bridgeCaseClass(TypeSymbol member) {
        return cd(new GeneratedClass.BridgeCase(pkg, member));
    }

    /** The class a union member occupies in the union: itself when this module declared it, its
     * bridge case otherwise. What {@code permits} lists, and what a value of the union is at the
     * {@code apply} boundary. */
    ClassDesc resultMemberClass(TypeSymbol member) {
        return isLocalMember(member) ? cd(member) : bridgeCaseClass(member);
    }

    /** Whether {@code member} is a type this module declares, and so carries its result unions
     * itself. What the language declares never is — no module emits a primitive or the prelude's
     * data — nor is a type another module emitted. */
    boolean isLocalMember(TypeSymbol member) {
        return !member.isDeclaredByLanguage()
                && member instanceof TypeSymbol.AtModule at && at.module().equals(pkg);
    }

    /** The members of {@code out} that reach their union through a bridge case, in the order the
     * union lists them. Empty when {@code out} is not a union, or when every member of it is a type
     * this module declared — then the union's JVM form and its Souther form are the same values and
     * neither boundary converts anything. */
    List<TypeSymbol> bridgedMembers(Type out) {
        return bridgedMembersIn(pkg, out);
    }

    private List<TypeSymbol> bridgedMembersIn(String module, Type out) {
        if (!(out instanceof Type.Union)) {
            return List.of();
        }
        List<TypeSymbol> bridged = new ArrayList<>();
        for (TypeSymbol member : AtomSpace.subjectAtoms(out, published)) {
            if (member.isDeclaredByLanguage()
                    || !(member instanceof TypeSymbol.AtModule at)
                    || !at.module().equals(module)) {
                bridged.add(member);
            }
        }
        return bridged;
    }

    /** The {@code $Fns} method name for a definition the module emits. A module-own helper keeps its
     * bare name; one reached under a qualified name ({@code List.foldFrom}) has the dot mangled to
     * {@code $}, since a JVM method name cannot contain a dot. Public because an {@code example} run
     * looks its operand's method up by this name, and the name is decided here. */
    public static String helperMethod(String name) {
        return name.replace('.', '$');
    }

    /** The JVM class of an output case. The built-in {@code DivisionByZero}/{@code NotANumber} need
     * no special case: their {@link TypeSymbol} names {@code souther.runtime}, which is where they are. An
     * invariant violation is no longer a case — it aborts (spec §algebraic-types, §violation-destination) —
     * so there is no 制約違反 case here. */
    ClassDesc caseClass(TypeSymbol typeName) {
        return cd(typeName);
    }

    /** The class a match case is tested against: a boxed/reference class for a primitive case,
     * otherwise the case's data class, which its resolved name already names. */
    ClassDesc matchCaseClass(TypeSymbol caseName) {
        if (!caseName.isPrimitive()) {
            return caseClass(caseName);
        }
        // The boxed carrier of the primitive the name spells, taken from the one table that says
        // which class carries which primitive rather than from a second copy of it here.
        Type.Prim prim = caseName.primitiveKind();
        ClassDesc boxed = prim == null ? null : JvmTypes.boxedPrim(prim);
        if (boxed != null) {
            return boxed;
        }
        // Option's `Some`/`None` are named here as well, being declared by no module, and never
        // reach this: an Option match dispatches on the runtime Option classes, not on an arm's
        // own name. Anything else naming no class is a resolution that should not have happened.
        throw new IllegalStateException("no class for the case " + caseName);
    }

    ClassDesc[] caseInterfaces(String name) {
        List<ClassDesc> ifaces = new ArrayList<>();
        for (GeneratedClass sum : caseToSums.getOrDefault(name, List.of())) {
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
    ClassDesc refTypeOrNull(Type t, ValueName.Behavior behaviorName) {
        return BehaviorAbi.refTypeOrNull(t,
                t instanceof Type.Union ? cdBehaviorResult(behaviorName) : null, this::caseClass);
    }

    Map<String, Type> fieldTypes(Hir.Data data) {
        return TypeOps.fieldTypes(data, symbols);
    }

    /**
     * {@code data}'s fields in the order a value lays them out — the components the class is
     * emitted with, and the parameters its constructor takes.
     *
     * <p><b>The order is asked of what answers it</b> ({@link TypeOps#fieldLayout}) and the types
     * are read by name. {@link #fieldTypes} says which type stands at each name and says nothing
     * about where a field stands, so an emitter taking a parameter order off it would be a second
     * place that decided the layout — and the day the two disagreed, a construction the check
     * lined up one way would be handed over another.
     *
     * <p>Asked once per class emitted and walked thereafter, so that every part of it — the
     * components, the fields, the constructor, the accessors — is laid out by the one answer.
     */
    SequencedMap<String, Type> laidOutFields(Hir.Data data) {
        SequencedMap<String, Type> out = new LinkedHashMap<>();
        Map<String, Type> types = fieldTypes(data);
        for (String field : TypeOps.fieldLayout(data, symbols)) {
            out.put(field, types.get(field));
        }
        return out;
    }

    Type successType(Hir.RetType ret) {
        return TypeOps.successType(ret);
    }

    // --- synthetic-class sink ---

    /** The next id for an escaping lambda's generated {@code $Fn} class (spec §blocks). */
    int nextLambdaId() {
        return lambdaCounter++;
    }

    void addSynth(GeneratedClass.Lambda lambda, byte[] bytes) {
        synthClasses.put(lambda, bytes);
    }

    /** The synthetic classes accumulated so far, for merging into the module output. */
    Map<GeneratedClass, byte[]> synthClasses() {
        return synthClasses;
    }
}
