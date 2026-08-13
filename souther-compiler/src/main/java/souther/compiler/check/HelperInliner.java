package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.StructuralCost;
import souther.compiler.ast.WrittenName;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.diag.msg.HelperMessage;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.OptionalInt;
import java.util.Set;
import java.util.function.IntFunction;

/**
 * Expands calls to helper {@code fn}s inline (spec §blocks: a named helper is the same as an inline block).
 *
 * <p>A helper fn is a {@code fn} with no matching behavior — it writes its own parameter types
 * (spec §fn-declaration) and, unlike a behavior fn, is not lowered to a class of its own. Instead every call
 * {@code h(a, b)} is rewritten to {@code let $k_p1 = a in let $k_p2 = b in <body>}, with the
 * helper's parameters α-renamed to fresh {@code $}-prefixed names so they cannot capture a caller
 * local (a source identifier never starts with {@code $}). Because the body is spliced into the
 * caller, the caller's construction-permission check, {@code depends on} inference, and codegen all
 * see the helper's constructions and injected calls directly — exactly as if the code had been
 * written inline (spec §blocks). Helpers must not recurse (directly or indirectly), which keeps the
 * expansion finite; a cycle is rejected up front.
 */
public final class HelperInliner {

    /**
     * Which declaration each name reaches, and the module they are reached in. A binding an expansion
     * makes belongs to a definition of that module, which is what tells it from the same helper
     * expanded elsewhere.
     *
     * <p>Not final: a recursive helper's own body is expanded against a table narrowed by its
     * parameters ({@link #inlineRecursiveBody}), and what that narrows is what a call reaches — never
     * what recurses, which {@link #recursive} settled over the table as it was built.
     */
    private HelperTable table;
    /**
     * The behaviors a body expanded here may name, with how many inputs each takes — the module's
     * own callable ones and the ones it borrows (spec {@code [#calling-a-behavior]}).
     *
     * <p>Apart from {@link #helpers} because a behavior is never expanded: what stands behind its
     * name may be a Java implementation, so a body that reached past it to the {@code let} would be
     * a second answer to the same name. All this holds is what reifying the name needs, which is its
     * arity; the query layer works out which behaviors are here, since which of them may be named is
     * a fact about the module rather than about any one body.
     */
    private Map<String, Integer> callableBehaviors = Map.of();
    /**
     * The values whose own answer this expansion was given, so that a reference to one need not
     * copy its body. Empty for every expansion that has no such answer — the tree the backend emits
     * from is one, and it copies every value as it always did.
     *
     * <p>Two answers rather than one, and they are read in {@link #settled}: the type a reference
     * stands under, and the constant a reference is written out as. A value has the first and may
     * have the second.
     */
    private Preserved settledValues = Preserved.NONE;
    private java.util.function.Function<ValueName, Object> settledConstants = _ -> null;
    /** What each declaration this table reaches calls, and which of them recurse. A function of the
     * table, so a narrowed table does not narrow it: what recurses was settled over the table as it
     * was built. */
    private final HelperGraph graph;
    /**
     * How much this pass has written into each body, which is what tells two of its writings apart.
     *
     * <p>Counted per body and not per pass. What a body is written into is not affected by what was
     * written into another — {@link BindingOwner.Expansion} says so of its ordinal — and one pass
     * expands many bodies: a helper checked on its own and then the behavior that calls it, every
     * definition a module publishes, every clause of a declaration's invariant. Counted across all of
     * them, a body's bindings moved when a body beside it gained an expansion or lost one to a
     * refusal, and a query answer that moves is a query answer everything below it is recomputed for.
     *
     * <p>Counted per body and not per writing, either. Two writings can share one body — one per
     * clause of an invariant, one per argument of a helper being checked — so a count that restarted
     * with each would give two of them the same binding.
     */
    private final Map<BindingOwner, Integer> written = new HashMap<>();
    /**
     * The values this expansion is inside, from the body being written down to here.
     *
     * <p>On the pass rather than in a {@link Writing}, because it is neither: a value's body is
     * substituted within the writing that names it, and the substitution of one value can carry the
     * expansion into another. It is a path through the tree being written, pushed and popped around
     * each substitution, and it is empty again whenever a body is finished with — including a body
     * that was refused partway through.
     */
    private final Set<String> substituting = new LinkedHashSet<>();

    /**
     * One writing of one body, and everything that is true only while it runs.
     *
     * <p>Four things were four fields, each saved and put back on its own, and one of them was left
     * standing after a refusal because the line that emptied it was on the path that did not run.
     * Held together they are made whole and dropped whole: what a writing holds is the writing's, and
     * a writing that did not finish takes it with it.
     *
     * @param into the body being written, which the bindings an expansion introduces belong under
     * @param binders the minter for those bindings — an expansion writes names no source wrote, so
     *                they belong to this writing rather than to the definition whose text it splices
     * @param dependencies which bindings the {@code depends on} parameters of a behavior's
     *                     {@code let} are; empty while writing anything else, because only a
     *                     behavior's {@code let} has them (spec §depends-on)
     * @param scopedLambdas the lambdas reached by a binding rather than by a name: one a block's
     *                      {@code let} binds, one handed to a function parameter. Apart from
     *                      {@link #table} because they are apart — a declaration is reached by a name
     *                      — and inside the writing because a lambda is in scope for as long as the
     *                      body holding it is being written and not one call longer
     */
    private record Writing(BindingOwner into, Ast.Binders binders, Set<BindingId> dependencies,
                           Map<BindingId, ScopedLambda> scopedLambdas) {

        Writing(BindingOwner into, Ast.Binders binders, Set<BindingId> dependencies) {
            this(into, binders, dependencies, new HashMap<>());
        }
    }

    /** The writing in force, or null outside one. Nothing public reads it without starting one. */
    private Writing writing;

    /**
     * A lambda reached by a binding, and where the author wrote it.
     *
     * <p>The two are one fact about one binding, so they are registered and dropped together. Held in
     * two tables they had to be put and removed twice, and a binding that made it into one of them
     * alone is a lambda a report cannot name or a name an expansion cannot reach.
     *
     * <p>{@code origin} is null where a {@code let} bound the lambda: the binding is then written
     * where the author wrote it, and a report about the lambda has nowhere else to point. It says
     * something only when a call site handed the lambda to a function parameter, because the lambda is
     * then registered under a synthetic name — a spelling that must never reach a diagnostic.
     */
    private record ScopedLambda(Ast.FnDef fn, LambdaOrigin origin) {

        ScopedLambda(Ast.FnDef fn) {
            this(fn, null);
        }
    }

    /** Where a lambda given to a function parameter was written: the parameter it fills, the helper
     * that declares that parameter, and the lambda's own position. Asked by the binding and not by
     * the spelling: two combinators nested one inside the other give their function parameters the
     * same name as often as not, and a report that found the outer one's lambda would point at
     * another author's line. */
    private record LambdaOrigin(String param, String owner, SourcePos pos) {}

    private HelperInliner(HelperTable table, HelperGraph graph) {
        this.table = table;
        this.graph = graph;
    }

    /** The body of {@code fn} in this module — what an expansion written into it belongs to. */
    public BindingOwner bodyOf(String fn) {
        return new BindingOwner.OfValue(table.module(), fn);
    }

    /** A helper is a fn whose name is not a behavior's; behavior fns are lowered on their own. The
     * prelude helpers join the inlining map under the qualified names they are reached by
     * ({@code Bool.not}), a module's own under the bare names it declared them with — so the two
     * never stand for one key, and how a call came to name one of them was settled before this. */
    public static HelperInliner forModule(Ast.Module module) {
        return forModule(module, Map.of());
    }

    /**
     * The same, with the definitions other modules publish to this one — each under the qualified name
     * it is reached by here, and each already closed by the module that declares it.
     *
     * <p>They join the inlining map but not {@code own}, which is what makes a recursive one come back
     * from {@link #injectedRecursiveHelpers} beside the recursive prelude helpers: neither is this
     * module's to declare, and both are this module's to emit. A module that reaches one only through
     * another module's body reaches it here too, because the walk that finds them follows calls rather
     * than imports.
     */
    public static HelperInliner forModule(Ast.Module module, Map<String, Ast.FnDef> imported) {
        HelperTable table = HelperTable.of(module, imported, InliningPolicy.FULL);
        HelperInliner inliner = new HelperInliner(table, HelperGraph.of(table));
        inliner.computeTakenOnRecursive(module);
        return inliner;
    }

    /**
     * The inlining an expansion needs, over the helpers alone.
     *
     * <p>Which helper a call expands to, and which calls are left standing because the helper recurses,
     * follow from the helpers and nothing else — so a body is expanded without reading the bodies
     * beside it. What does read the whole module is {@link #injectedRecursiveHelpers}: which prelude
     * recursive helpers a module emits as its own methods is a fact about the module, not about any
     * one call, and {@link #forModule} is what answers it. A module that has already taken those on as
     * its own fns has them here like any other helper, so both say the same thing about it.
     */
    public static HelperInliner forHelpers(String module, Map<String, Ast.FnDef> own) {
        return forHelpers(module, own, InliningPolicy.FULL);
    }

    /**
     * The same, resolving only what {@code policy} says to resolve.
     *
     * <p>{@link InliningPolicy#DISCHARGE} leaves the standard library out of the table, so a call to
     * one of its operations is not a helper call here and survives as written. Nothing else changes:
     * a module's own helper is expanded, and a recursive call is left standing, by the same rules.
     */
    public static HelperInliner forHelpers(String module, Map<String, Ast.FnDef> own,
                                           InliningPolicy policy) {
        return forHelpers(module, own, Map.of(), policy);
    }

    /**
     * The same, with the definitions other modules publish to this one joining the table.
     *
     * <p>They are in the table and not in {@code own}, as they are for {@link #forModule}: an imported
     * definition is one this module expands and not one it declares.
     */
    public static HelperInliner forHelpers(String module, Map<String, Ast.FnDef> declared,
                                           Map<String, Ast.FnDef> imported, InliningPolicy policy) {
        HelperTable table = HelperTable.of(module, declared, Map.of(), imported, policy);
        return over(table, HelperGraph.of(table));
    }

    /**
     * The inlining over a table and the graph of that table, both worked out elsewhere.
     *
     * <p>What a call reaches and what recurses are facts about a module's declarations, so a compile
     * asks them once and every body of that module is expanded against the same two answers. The
     * factories above are for a caller holding declarations rather than answers.
     */
    public static HelperInliner over(HelperTable table, HelperGraph graph) {
        return new HelperInliner(table, graph);
    }

    /**
     * The same, told which behaviors a body expanded here may name and how many inputs each takes.
     *
     * <p>Told rather than worked out: which behaviors those are follows from the declarations of
     * this module and of the ones it imports, which is not what this pass reads. A body expanded
     * without being told names none of them, and a name it cannot reify is left as it was written
     * for the check to report.
     */
    public HelperInliner namingBehaviors(Map<String, Integer> arities) {
        this.callableBehaviors = Map.copyOf(arities);
        return this;
    }

    /**
     * The same, told what the values named in {@code settled} were settled as, so that a reference
     * to one of them is not copied.
     *
     * <p>For the checks that read a definition on its own. A definition is checked against what the
     * definitions it names were settled as, which is what a check of each of them already worked
     * out; copying the body instead re-derives that answer once per name that reaches it, so a
     * chain of values costs the chain again per link. What the backend emits is the other question
     * and unchanged: a value is substituted where it is named (ADR-0072), and the tree it is
     * substituted into is not built here.
     */
    public HelperInliner readingSettledValues(Preserved settled,
                                             java.util.function.Function<ValueName, Object> constants) {
        this.settledValues = settled;
        this.settledConstants = constants;
        return this;
    }

    /** The helpers a module declares: the fns its source wrote that implement no behavior, keyed by
     * the name it declared each under. Not what it took on to emit — that is {@link #takenOnBy}, and
     * the two are separate components of the module so that this answer is the same at every stage. */
    public static Map<String, Ast.FnDef> helpersOf(Ast.Module module) {
        return keyed(module, module.fns());
    }

    /** The helpers a module emits without having declared them, keyed by the name it reaches each by.
     * Empty until the pass that works out what the module reaches has run. */
    public static Map<String, Ast.FnDef> takenOnBy(Ast.Module module) {
        return keyed(module, module.takenOn());
    }

    private static Map<String, Ast.FnDef> keyed(Ast.Module module, List<Ast.FnDef> fns) {
        Set<String> behaviorNames = new HashSet<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            behaviorNames.add(b.name());
        }
        Map<String, Ast.FnDef> out = new LinkedHashMap<>();
        for (Ast.FnDef fn : fns) {
            if (!behaviorNames.contains(fn.name())) {
                out.put(fn.name(), fn);
            }
        }
        return out;
    }

    /**
     * The recursive helpers this module reaches and does not declare, by the qualified name it
     * reaches each of them by ({@code List.foldFrom}, {@code pricing.sumDown}).
     *
     * <p>A recursive helper is not inlined — it would expand forever — so it is emitted as one of
     * this module's own methods, exactly like a recursive helper the module declared (see {@link
     * #injectedRecursiveHelpers}). That holds whoever declared it: the standard library, or a module
     * that published one, or published something that calls one. Only the ones actually reached are
     * emitted.
     */
    private final Set<String> takenOnRecursive = new java.util.LinkedHashSet<>();

    /** The helpers this module's example rows apply, which need a method for that reason alone. */
    private final Set<String> exampleHelpers = new java.util.LinkedHashSet<>();

    /**
     * Walks everything the module writes — its fn bodies, its data invariants, its rows — collecting
     * the recursive helpers it reaches and does not declare. Those it must emit as methods of its own.
     *
     * <p>Reached, which is wider than called. A helper written where a value goes is eta-expanded into
     * a call, and a value's body stands wherever the value is named, so a helper is reached through
     * either. Both were once left to a caller that joined the definitions this module's imports
     * publish into what it has as fns of its own: that join answered yes for every published helper
     * whether this module reached it or not, and so covered what this walk was not finding.
     */
    private void computeTakenOnRecursive(Ast.Module module) {
        Set<String> named = new LinkedHashSet<>();
        Deque<Ast.Expr> work = new ArrayDeque<>();
        for (Ast.FnDef fn : module.fns()) {
            work.add(fn.writtenBody());
        }
        for (Ast.Def d : module.defs()) {
            if (d instanceof Ast.Data data) {
                for (Ast.InvariantClause clause : data.invariants()) {
                    work.add(clause.expr());
                }
            }
        }
        forEachExampleExpr(module, work::add);
        followingValues(work, table.reachable(),
                e -> helpersNamedIn(e, table.reachable(), named));
        for (String name : graph.reachedFrom(named)) {
            if (graph.recurses(name) && !table.held().containsKey(name)) {
                takenOnRecursive.add(name);
            }
        }
        exampleHelpers.addAll(exampleHelpers(module, table.reachable()));
        exampleHelpers.removeAll(takenOnRecursive);
        exampleHelpers.removeIf(graph::recurses);   // already emitted as a recursive helper
    }

    /** Every expression an {@code example} or a {@code fake} of {@code module} writes: a row's inputs,
     * its {@code with} values, its expected result, and a fake table's inputs and outputs. A helper
     * named in any of them is applied when the row is evaluated, so all of them are read here. */
    private static void forEachExampleExpr(Ast.Module module, java.util.function.Consumer<Ast.Expr> f) {
        for (Ast.Example ex : module.examples()) {
            for (Ast.ExampleRow row : ex.rows()) {
                row.inputs().forEach(f);
                for (Ast.With w : row.withs()) {
                    f.accept(w.value());
                }
                f.accept(row.expected());
            }
        }
        for (Ast.Fake fake : module.fakes()) {
            for (Ast.FakeRow row : fake.rows()) {
                if (row.inputs() != null) {   // a default row matches anything and writes none
                    row.inputs().forEach(f);
                }
                f.accept(row.output());
            }
        }
    }

    /**
     * The helpers an {@code example} row of {@code module} applies, keyed as {@code table} keys them.
     *
     * <p>A row is a fixture and a helper is run rather than expanded into it (ADR-0077), so each of
     * these needs a method to apply — which is the one reason a non-recursive helper is emitted. What
     * such a helper reaches is expanded into it before it is emitted, so this is what a row names and
     * not its transitive closure; a recursive helper it reaches is a method already.
     *
     * <p>A helper whose body produces a function is not here: it has no value to hand back, and a row
     * applying one is refused where it is evaluated, by that reason. An intrinsic has no body either,
     * and is collected below rather than here — it is emitted from a body written for it (#680).
     */
    public static Set<String> exampleHelpers(Ast.Module module, Map<String, Ast.FnDef> table) {
        Set<String> called = new LinkedHashSet<>();
        Deque<Ast.Expr> work = new ArrayDeque<>();
        forEachExampleExpr(module, work::add);
        // What a row applies, so a helper it merely names is not one: a row is a fixture and holds no
        // function, and the reason a method is emitted here is that the row runs the helper.
        followingValues(work, table, e -> helperCallsIn(e, table, called));
        Set<String> out = new LinkedHashSet<>();
        for (String name : called) {
            Ast.FnDef helper = table.get(name);
            if (helper != null && helper.body() instanceof Ast.FnBody.Written w
                    && !helper.params().isEmpty() && !Elaborator.producesFunction(w.expr())) {
                out.add(name);
            }
        }
        // The intrinsics a row applies, collected on their own because the table has none of them:
        // it holds what may be expanded into a body, and an intrinsic is lowered at its call site
        // instead. That is a fact about the backend, and a row that applies one is asking the same
        // thing of it as a row applying any other library function (#680).
        Deque<Ast.Expr> kernels = new ArrayDeque<>();
        forEachExampleExpr(module, kernels::add);
        // Named as they are emitted, not as they are written. This set is what decides which fns
        // survive lowering, and what has to survive for a kernel is the wrapper — the kernel's own
        // name belongs to the call the wrapper makes.
        followingValues(kernels, table, e -> intrinsicCallsIn(e, out));
        return out;
    }

    /**
     * Adds the intrinsic each application in {@code e} reaches, where a fixture could apply it.
     *
     * <p>Kept apart from {@link #helperCallsIn}, which feeds the recursion graph. What recurses is
     * decided from calls between bodies that have one; an intrinsic has no body and belongs to
     * neither that question nor that answer.
     *
     * <p>A kernel a fixture may not apply is not collected, and which those are is {@link
     * #decidedByEachCall} — the same reading that refuses one where a fixture is built. Asked once,
     * because a kernel one reading admitted and the other missed would be admitted by the fixture and
     * then told it has no method, which is the representation-shaped refusal this removes.
     */
    private static void intrinsicCallsIn(Ast.Expr e, Set<String> out) {
        if (e instanceof Ast.Apply call && call.function() instanceof Ast.Var.Denoting
                && call.denotes() instanceof ValueName.Stdlib) {
            Prelude.PreludeEntry entry = Prelude.entry(call.reaches());
            if (entry != null && entry.declaration().body() instanceof Ast.FnBody.Intrinsic
                    && !entry.declaration().params().isEmpty()
                    && appliableInAFixture(entry.signature().params())) {
                out.add(intrinsicWrapperName(call.reaches()));
            }
        }
        Ast.forEachChild(e, c -> intrinsicCallsIn(c, out));
    }

    /** Whether a declaration taking {@code paramTypes} is one a fixture may apply. */
    private static boolean appliableInAFixture(List<Type> paramTypes) {
        for (Type t : paramTypes) {
            if (decidedByEachCall(t)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether {@code t} leaves something for each call to decide, which a fixture has no call to do:
     * it is built before there is a call that could settle it.
     *
     * <p>The one reading of that question. It decides which kernels a method is emitted for and which
     * calls a fixture may apply, and those are the same question — a second reading of it is a second
     * set, free to come apart from the first.
     */
    public static boolean decidedByEachCall(Type t) {
        return Type.mentions(t, x -> x instanceof Type.Var);
    }

    /**
     * The name a kernel's wrapper is emitted under: where its method goes, and not what the function
     * is. A report names the kernel the row applied; only a method lookup takes this.
     *
     * <p>Not the kernel's own name. Under that name the emitted method would be a helper the table
     * reaches, and a body calling {@code String.length} would expand into it — into a body whose one
     * call is to {@code String.length}, which is the same call again. The name is written nowhere a
     * source could spell, so what is emitted here is reached from a fixture and from nothing else.
     */
    public static String intrinsicWrapperName(String reached) {
        return INTRINSIC_PREFIX + reached;
    }

    /** The kernel {@code emitted} wraps, or null where it is not one of these at all. */
    private static String intrinsicWrapped(String emitted) {
        return emitted.startsWith(INTRINSIC_PREFIX)
                ? emitted.substring(INTRINSIC_PREFIX.length()) : null;
    }

    private static final String INTRINSIC_PREFIX = "$intrinsic.";

    /**
     * {@code kernel} as a helper with a body: it applies the intrinsic to its own parameters.
     *
     * <p>What the module could not take on before. An intrinsic has no body to emit, so nothing was
     * emitted and a row applying one was told a rule about the standard library; the eta-expansion is
     * a body, and the backend lowers the one call in it exactly as it lowers that call anywhere else.
     * So this materialises a method without teaching anything a second way to run a kernel.
     */
    private static Ast.FnDef fixtureWrapper(String reached, Ast.FnDef kernel) {
        List<Ast.Expr> args = new ArrayList<>();
        for (Ast.FnParam p : kernel.params()) {
            args.add(Ast.Var.local(p.binder(), kernel.pos()));
        }
        ValueName.Stdlib target = Prelude.operation(reached);
        Ast.Expr body = new Ast.Apply(reached, target, new ReachName.OfLibrary(target), args,
                ConstructionOrigin.own(), kernel.pos(), null);
        return kernel.reachedAs(intrinsicWrapperName(reached))
                .withBody(new Ast.FnBody.Written(body));
    }

    /** As {@link #exampleHelpers(Ast.Module, Map)}, for the module this inliner reads: the ones it must
     * emit as methods, without those a recursion already emits. */
    public Set<String> exampleHelpers() {
        return exampleHelpers;
    }

    /** The example-applied helpers this module does not declare — a published one, or a prelude one —
     * renamed to the qualified name they are reached by, so the module takes them on as its own fns and
     * emits them beside its own, as it does for a recursive one it reaches. */
    public Map<String, Ast.FnDef> injectedExampleHelpers() {
        Map<String, Ast.FnDef> out = new java.util.LinkedHashMap<>();
        for (String name : exampleHelpers) {
            if (table.held().containsKey(name)) {
                continue;
            }
            if (intrinsicWrapped(name) instanceof String kernel) {
                // A kernel, which the table does not reach: it has no body to expand into a caller,
                // which is the only thing that table holds. Its wrapper is written here.
                out.put(name, fixtureWrapper(kernel, Prelude.entry(kernel).declaration()));
                continue;
            }
            out.put(name, table.reached(name).reachedAs(name));
        }
        return out;
    }

    /** The recursive helpers this module emits as methods: the ones it declares, plus the ones it
     * reaches and took on to emit — a library one, or one another module published (spec §fn-declaration). A
     * call to any of them is left standing by {@link #inline}. The graph's own {@code recursive} set
     * additionally holds recursive helpers the module does not reach at all, so {@code inline} never
     * expands one that slips in through a nested body.
     *
     * <p>Answered in declaration order, which is the order a check reporting one of them reports in.
     * The order is the graph's and is carried, not rebuilt. */
    public java.util.SequencedSet<String> recursiveHelpers() {
        java.util.SequencedSet<String> result = new java.util.LinkedHashSet<>();
        for (String name : graph.recursive()) {
            if (table.held().containsKey(name)) {
                result.add(name);
            }
        }
        result.addAll(takenOnRecursive);
        return result;
    }

    /** The recursive helpers this module reaches and does not declare, renamed to the qualified names
     * it reaches them by so they are emitted as the module's own methods — a library {@code let
     * foldFrom} is reached as {@code List.foldFrom}, and its self-call already reads {@code
     * List.foldFrom}. Which module declared one is not in that name and is read off the declaration
     * ({@link Ast.FnDef#declaredIn}). */
    public Map<String, Ast.FnDef> injectedRecursiveHelpers() {
        Map<String, Ast.FnDef> out = new java.util.LinkedHashMap<>();
        for (String qualified : takenOnRecursive) {
            Ast.FnDef def = table.reached(qualified);
            out.put(qualified, def.reachedAs(qualified));
        }
        return out;
    }

    /**
     * The module's helper fns, keyed by the name it reaches each of them by — what it declared, and
     * what it took on to emit as a method of its own.
     *
     * <p>Both, because both are emitted here and both are checked here. Which module declared one is
     * not read off this map or off the key: the declaration says it
     * ({@link Ast.FnDef#declaredBy}), and a check whose rule is about the declaring module — what
     * may be walked, what must be proven total — asks it there.
     */
    public Map<String, Ast.FnDef> held() {
        return table.held();
    }

    /**
     * A definition {@code module} publishes, closed so that it means in a reader what it means here.
     *
     * <p>Closing is expansion: the module's own values and non-recursive helpers are substituted into
     * the body, so no bare name of this module is left for the reader to read against its own
     * definitions (ADR-0067). A recursive helper is the one thing expansion cannot remove — it is
     * lowered to a method, so the call stays a call — and it is qualified here instead, under the
     * module that declares it. The reader emits that method as one of its own, exactly as it already
     * does for a recursive prelude helper it reaches.
     *
     * <p>What comes back is named qualified too. The name is the definition's identity across
     * modules, and a bare one is only how a reader happens to write it: two modules may publish a
     * {@code tally}, and a reader may reach one of them without importing it at all — through the
     * body of something else it imported.
     */
    public Ast.FnDef closeAcross(Ast.FnDef fn, String module) {
        Ast.Expr closed = graph.recurses(fn.name())
                ? inlineRecursiveBody(fn) : inline(fn.writtenBody(), bodyOf(fn.name()));
        return fn.reachedAs(HelperNames.qualified(module, fn.name()))
                .withBody(new Ast.FnBody.Written(
                        HelperNames.publishedBy(HelperNames.qualifyHelpersOf(closed, module), module)));
    }

    /** The module these helpers belong to — the one whose bodies this expands into. */
    public String moduleName() {
        return table.module();
    }

    /** The declaration reached by {@code name} across the prelude and the module's own helpers, or
     * null where the name reaches none. For a reader walking a set of names this pass answered with —
     * the recursive helpers, say. A reader holding a call asks {@link #applied} instead, because what
     * a call applies is not decided by how it is spelled. */
    public Ast.FnDef helper(String name) {
        return table.reached(name);
    }

    /** The body {@code call} applies, or null where it applies something no body stands behind. */
    public Ast.FnDef applied(Ast.Apply call) {
        return appliedHelper(call);
    }

    /** {@code fold} is the one privileged loop primitive that takes a block (spec §stdlib-list); its block is
     * the first argument and has two parameters (`(acc, x)`, spec §pipe). A bare name passed in its
     * place is sugar for a block that wraps a call. The map is from the combinator name to the block's
     * argument index. The other combinators (map/filter/all/any) are ordinary prelude helpers derived
     * from fold (ADR-0028), so they need no such desugaring — a name reaches their function parameter
     * directly. */
    private static final Map<String, Integer> BLOCK_ARG = Map.of("List.foldFrom", 0);

    /** The call a sugared name becomes, written out: what it becomes and what it supplies are the
     * library's to say ({@link Prelude#rewriteOf}), and this is where it is done. {@code List.fold(step,
     * seed, xs)} is {@code List.foldFrom(step, seed, xs, 0)} — the walk from the head. Rewriting here,
     * before inlining, means the step reaches {@code foldFrom} (the one recursive helper) directly
     * rather than through a wrapper that would pass the function on as a value. */
    private static Ast.Apply desugar(Ast.Apply call) {
        if (!(call.function() instanceof Ast.Var.Denoting)) {
            return call;   // it reaches no library name, so there is no sugar to write out
        }
        Prelude.Rewrite rewrite = Prelude.rewriteOf(call.reaches());
        if (rewrite == null || call.args().size() != rewrite.keptArgs()) {
            return call;
        }
        List<Ast.Expr> args = new ArrayList<>(call.args());
        for (int supplied : rewrite.supplied()) {
            // an argument the rewrite supplies, which no one wrote
            args.add(new Ast.IntLit(supplied, call.pos(), null));
        }
        // The library name this reaches for is the pass's; where it stands is the callee's.
        return new Ast.Apply(
                Ast.Var.respelled(rewrite.target().qualified(), rewrite.target(),
                        new ReachName.OfLibrary(rewrite.target()), call.function().pos(),
                        call.function().region()),
                args, ConstructionOrigin.own(), call.pos(), call.region());
    }

    /** Inlines a recursive helper's own body, expanding the non-recursive helper calls it makes while
     * leaving its own parameters alone. A parameter that shares a module helper's name — {@code
     * foldFrom}'s function parameter {@code step} in a module that also defines a helper {@code step} —
     * is a parameter application, not a call to that helper, so the same-named helpers are hidden while
     * the body is expanded. */
    public Ast.Expr inlineRecursiveBody(Ast.FnDef h) {
        List<String> parameters = new ArrayList<>();
        for (Ast.FnParam p : h.params()) {
            parameters.add(p.name());
        }
        HelperTable outer = table;
        // Narrowed, not rebuilt: what a call reaches changes, what recurses does not. A graph taken
        // over the narrowed table would find this very helper non-recursive and expand its own call
        // forever.
        table = table.hiding(parameters);
        try {
            return inline(h.writtenBody(), bodyOf(h.name()));
        } finally {
            table = outer;
        }
    }

    /**
     * What this application decides for the variables {@code helper}'s signature left open — one
     * fresh variable per variable it wrote, over its parameters and its declared return together.
     * Empty where it wrote none, which is every call of a helper that names its types outright.
     *
     * <p>Every unsolved variable in a helper's declared types is that helper's own: a variable enters
     * a type only where the core writes one in a signature or where a helper's own settling mints one
     * for its parameters, and a reference to a declared type carries none. So renaming by name over
     * the whole signature at once binds nothing it should not.
     */
    private static Map<String, Type> instantiation(Ast.FnDef helper, BindingOwner mine) {
        Map<String, Type> applied = new LinkedHashMap<>();
        for (Ast.FnParam p : helper.params()) {
            collectVariables(p.type(), mine, applied);
        }
        collectVariables(helper.declaredReturn(), mine, applied);
        return applied;
    }

    private static void collectVariables(Ast.RetType declared, BindingOwner mine,
                                         Map<String, Type> applied) {
        if (declared == null || !mentionsRetTypeVar(declared)) {
            return;
        }
        Type.mentions(TypeOps.resolveParamType(declared, null), t -> {
            if (t instanceof Type.Var v) {
                applied.computeIfAbsent(v.name(), name -> new Type.MetaVar(mine, name));
            }
            return false;   // a collector, not a test: every position is visited
        });
    }

    /**
     * What a function argument is declared as where it comes from, or null where nothing this
     * expansion can see declares it.
     *
     * <p>A name standing for a function an enclosing call supplied is one this expansion is holding,
     * and what that call declared of it is written on it. Every other name — a helper's own
     * parameter, a binding holding a function — is declared where it is bound, and the scope the
     * boundary is read in is what answers for it.
     */
    private Ast.RetType arrivesAs(Ast.Expr arg) {
        if (!(arg instanceof Ast.Var.Denoting v)) {
            return null;
        }
        Ast.FnDef is = expands(v.denotes(), v.reaches());
        if (is == null || is.declaredReturn() == null) {
            return null;
        }
        List<Ast.RetType> params = new ArrayList<>();
        for (Ast.FnParam p : is.params()) {
            if (p.type() == null) {
                return null;   // it does not say what it takes, so it says nothing whole
            }
            params.add(p.type());
        }
        return new Ast.RetType(
                List.of(new Ast.FnType(params, is.declaredReturn(), is.pos())), is.pos());
    }

    /** What a function parameter's declared type says, with what this application decided written
     * into it — or null where the parameter's type is not a lone function type. */
    private static Ast.FnType declaredFn(Ast.RetType declared, Map<String, Type> applied) {
        if (declared == null
                || !(TypeOps.substitute(TypeOps.resolveParamType(declared, null), applied)
                        instanceof Type.FnOf fn)) {
            return null;
        }
        List<Ast.RetType> params = new ArrayList<>();
        for (Type p : fn.params()) {
            params.add(stating(p, declared.pos()));
        }
        return new Ast.FnType(params, stating(fn.result(), declared.pos()), declared.pos());
    }

    /** {@code t} as a written type with no surface text: what it denotes is decided, and no source
     * stands for it. */
    private static Ast.RetType stating(Type t, SourcePos pos) {
        return new Ast.RetType(List.of(Ast.TypeRef.of(t, pos)), pos);
    }

    /** {@code declared} with what this application decided written into it, or as it stands where it
     * left nothing open. The type is written as a reference with no surface text: what it denotes is
     * decided, and no source stands for it. */
    private static Ast.RetType instantiated(Ast.RetType declared, Map<String, Type> applied) {
        if (declared == null || applied.isEmpty() || !mentionsRetTypeVar(declared)) {
            return declared;
        }
        Type at = TypeOps.substitute(TypeOps.resolveParamType(declared, null), applied);
        return new Ast.RetType(List.of(Ast.TypeRef.of(at, declared.pos())), declared.pos());
    }

    /** Whether a declared type has a type variable inside it. A generic declared return ({@code
     * Map.updateOrInsert}'s {@code Map<'k, 'a>}) says nothing concrete at a call site, so it is not carried —
     * the caller's own arguments are what fix those variables. */
    private static boolean mentionsRetTypeVar(Ast.RetType ret) {
        return ret != null && ret.cases().stream().anyMatch(HelperInliner::mentionsTypeVar);
    }

    /**
     * Asked of what the reference denotes, not of how it was spelled. A reference a
     * helper's own settling wrote carries its type and no surface text at all
     * ({@link Ast.TypeRef#of}), so reading the spelling answers no about every one of them.
     *
     * <p>The whole reference is in what it denotes: {@code List<'a>} resolves to a type that holds
     * the variable, so the argument and a tuple's elements are not walked again here. This runs
     * after resolution, and a reference that has not been read is refused by {@link
     * Ast.TypeRef#denotes()} rather than answered off its spelling.
     */
    static boolean mentionsTypeVar(Ast.TypeTerm term) {
        if (term instanceof Ast.FnType fn) {
            return fn.params().stream().anyMatch(HelperInliner::mentionsRetTypeVar)
                    || mentionsRetTypeVar(fn.result());
        }
        if (!(term instanceof Ast.TypeRef ref)) {
            return false;
        }
        return Type.mentions(ref.denotes(), t -> t instanceof Type.Var);
    }

    /**
     * The parameters a call's callee declares, as the caller wrote the name: a helper's own, or —
     * for the {@code List.fold} sugar — {@code foldFrom}'s without the index the sugar supplies.
     * Null when the name is not a helper (a builtin, an injected behavior, or unknown).
     */
    private List<Ast.FnParam> declaredParams(Ast.Apply call) {
        if (!(call.function() instanceof Ast.Var.Denoting)) {
            return null;   // it reaches no declaration, so none of them declares anything
        }
        Prelude.Rewrite rewrite = Prelude.rewriteOf(call.reaches());
        if (rewrite != null && call.args().size() == rewrite.keptArgs()) {
            Ast.FnDef target = table.reached(rewrite.target().qualified());
            return target == null ? null : target.params().subList(0, rewrite.keptArgs());
        }
        Ast.FnDef helper = table.reached(call.reaches());
        return helper == null ? null : helper.params();
    }

    /**
     * Rejects a lambda written on a parameter that takes a value. The standard library takes its
     * function first and its collection last (spec §pipe), so the arguments given the other way round
     * are the common first mistake — and left alone the lambda travels on as an ordinary value, to be
     * reported deep in the expansion as a block that escaped, against a rule about first-class
     * functions the caller has not met yet. Reported here, at the call, the parameter it landed on and
     * the one that takes the function are both still in hand, so the order can be named.
     *
     * <p>Checked against the name as written, before {@code List.fold} desugars to {@code foldFrom}:
     * the report names the caller's own call, not what the sugar expands to. A block with no
     * parameters is a braced block, not a lambda, and is left to the checker.
     */
    private void checkFunctionArgumentPlacement(Ast.Apply call) {
        List<Ast.FnParam> params = declaredParams(call);
        if (params == null || params.size() != call.args().size()) {
            return;   // not a helper, or an arity mismatch reported with the call itself
        }
        int fnParam = -1;
        for (int i = 0; i < params.size(); i++) {
            if (params.get(i).type() != null && params.get(i).type().asFn() != null) {
                fnParam = i;
                break;
            }
        }
        for (int i = 0; i < params.size(); i++) {
            Ast.RetType declared = params.get(i).type();
            if (declared == null || declared.asFn() != null
                    || !(call.args().get(i) instanceof Ast.Block lambda) || lambda.params().isEmpty()) {
                continue;
            }
            String param = params.get(i).name();
            if (fnParam < 0) {
                throw CompileException.of(Diagnostic.at(lambda.pos())
                        .say(new HelperMessage.ThisArgumentTakesNoFunction(call.written(),
                                String.valueOf(i + 1), param))
                        .build());
            }
            String shape = params.stream().map(Ast.FnParam::name)
                    .collect(java.util.stream.Collectors.joining(", "));
            throw CompileException.of(Diagnostic.at(lambda.pos())
                    .say(new HelperMessage.TheFunctionGoesToAnotherArgument(call.written(),
                            String.valueOf(i + 1), param, String.valueOf(fnParam + 1),
                            params.get(fnParam).name()))
                    .hint(new HelperMessage.WriteTheCallThisWay(call.written(), shape))
                    .build());
        }
    }

    /**
     * The body a call applies, or null where it applies something no body stands behind.
     *
     * <p>What is applied follows from what the call denotes. A binding applies the lambda bound
     * there, if one is; a declared name applies the declaration it reaches. Neither is asked of the
     * other, so a parameter spelled like a helper is the parameter, and a lambda bound to a name a
     * module declares is the lambda — with nothing to tell the two apart by.
     */
    private Ast.FnDef appliedHelper(Ast.Apply call) {
        if (call.function() instanceof Ast.Var.Unanswered) {
            return null;   // it names nothing, so no body stands behind it
        }
        return expands(call.denotes(), call.reaches());
    }

    /**
     * The body {@code denotes} stands for here, or null where no body stands behind it.
     *
     * <p>The one place that answers it, so a name applied and a name handed over get the same answer.
     * {@code reachedBy} is how the name is written here — bare for a definition of this module,
     * qualified for the library and for what another module publishes — which is the namespace the
     * table is keyed by; which namespace to look in is decided by the denotation, never by the text.
     */
    private Ast.FnDef expands(ValueName denotes, String reachedBy) {
        return switch (denotes) {
            // applying something that is not a name: what is applied is worked out by the expression,
            // and no declaration stands behind it
            case null -> null;
            // A binding holds a lambda only inside the writing that put it there, so asked outside
            // one — which is where a check reads a call without expanding anything — a binding stands
            // for nothing this can answer with. It was answered that way before by a table that
            // happened to be empty there; it is answered that way now because there is no writing to
            // ask.
            case ValueName.Local local -> {
                ScopedLambda lambda = writing == null ? null
                        : writing.scopedLambdas().get(local.id());
                yield lambda == null ? null : lambda.fn();
            }
            case ValueName.Helper _, ValueName.Stdlib _ -> table.reached(reachedBy);
            // a construction, an injected behavior, `None`, or a name that denotes nothing: each is
            // applied by something other than an expansion, and each is reported where it belongs
            case ValueName.OfType _, ValueName.Behavior _, ValueName.Builtin _ -> null;
        };
    }

    /**
     * The arguments of a call that stays a call, with a dependency handed over by name replaced by
     * the block that forwards to it: {@code depth(code, fetch)} becomes {@code depth(code, (c) ->
     * fetch(c))}, which spec §blocks says is the same thing.
     *
     * <p>Where the callee is expanded the two already are the same thing — the expansion substitutes
     * the argument's name into the parameter's applications, so the name only ever stands in a call.
     * A recursive helper is lowered to a method instead (spec §fn-declaration), which leaves the argument
     * standing as a value, and a {@code depends on} parameter is reached through the behavior it
     * names rather than bound to a slot. Forwarding here is what makes the two callees say the same
     * thing about the same argument.
     *
     * <p>What is forwarded is the parameter, not every name spelled like it: the argument is matched
     * against the binder its name was answered with. A binding in force wins over the declaration it
     * shadows (spec §fn-rules), so a local named after a dependency is a local, and wrapping it would
     * both call the wrong thing and report a value as an uncallable name.
     */
    private List<Ast.Expr> forwardDependencies(Ast.FnDef callee, List<Ast.Expr> args) {
        if (callee == null || writing.dependencies().isEmpty()) {
            return args;
        }
        List<Ast.Expr> out = new ArrayList<>(args);
        for (int i = 0; i < callee.params().size() && i < out.size(); i++) {
            Ast.RetType declared = callee.params().get(i).type();
            Ast.FnType want = declared == null ? null : declared.asFn();
            if (want == null || !(out.get(i) instanceof Ast.Var v)
                    || !(v.denotes() instanceof ValueName.Local local)
                    || !writing.dependencies().contains(local.id())) {
                continue;
            }
            out.set(i, etaExpand(v, want.params().size(), _ -> "$" + next() + "_" + v.name()));
        }
        return out;
    }

    /** As {@link #inline(Ast.Expr, BindingOwner)}, for the body of a behavior {@code let} whose
     * {@code depends on} parameters are the trailing bindings named in {@code dependencies}. */
    public Ast.Expr inline(Ast.Expr e, Set<BindingId> dependencies, BindingOwner into) {
        heldToTheBound(e);
        return writing(into, dependencies, () -> inline(e));
    }

    /**
     * Rewrites every helper call in {@code e} to its inlined body, into {@code into}.
     *
     * <p>{@code into} is the body being written: the bindings an expansion introduces belong to it,
     * so two copies of one helper's body spliced into two definitions do not answer as one binding.
     */
    public Ast.Expr inline(Ast.Expr e, BindingOwner into) {
        heldToTheBound(e);
        return writing(into, Set.of(), () -> inline(e));
    }

    /**
     * Runs {@code expansion} as one writing into {@code into}.
     *
     * <p>The writing is a value and it is made whole: nothing it holds is left from the writing
     * before, and nothing it holds outlives it — including where an expansion was refused partway
     * through, which is a thing that happens, because a caller records a refusal and hands the next
     * body to the same pass.
     *
     * <p>A writing may hold another. A helper's body is expanded while the body that called it is
     * being expanded, so the one in force is put back when this one is done rather than dropped.
     */
    private Ast.Expr writing(BindingOwner into, Set<BindingId> dependencies,
                             java.util.function.Supplier<Ast.Expr> expansion) {
        Writing outer = writing;
        // Numbered among what this pass has written into that body, so a second writing into it — a
        // second clause of one invariant, a second argument of one helper — writes bindings of its
        // own rather than the first one's over again.
        writing = new Writing(into,
                new Ast.Binders(new BindingOwner.Synthesized(into, BindingOwner.Pass.INLINER,
                        written.merge(into, 1, Integer::sum) - 1)),
                dependencies);
        try {
            return expansion.get();
        } finally {
            writing = outer;
        }
    }

    /**
     * Refuses a body whose expansion would say more than a definition holds.
     *
     * <p>Before the expansion and not after it. What the expansion builds is what a walk after it
     * descends, so a body that composed past the bound is one nothing downstream can be asked
     * about — and the expansion that built it descends it too, so finding out by running it is
     * finding out by running out.
     *
     * <p>Counted over what the source wrote, with each name standing for what it reaches. The body
     * as written was already held to the bound where it was written; what is asked here is the
     * larger question, which only substitution can answer: a definition can be small and name three
     * that are not.
     */
    private void heldToTheBound(Ast.Expr body) {
        StructuralCost.Composed composed = StructuralCost.composed(body, this::substitutedAt);
        if (composed.isPastTheBound()) {
            throw CompileException.of(Diagnostic
                    .say(new DeclarationMessage.SubstitutingAValueIsMoreStructureThanIsHeld(
                            composed.past().name(), StructuralCost.MAX))
                    .at(composed.past().pos())
                    .hint(new DeclarationMessage.WriteItAsABehaviorOfItsOwn())
                    .build());
        }
    }

    /** The body {@code name} would put here, or null where the name stands for itself — asked as
     *  {@link #valueOf} and {@link #expandCall} ask it, so what is counted is what is spliced. */
    private Ast.Expr substitutedAt(Ast.Var name) {
        if (!(name instanceof Ast.Var.Denoting)
                || !(name.denotes() instanceof ValueName.Helper)
                || graph.recurses(name.reaches())) {
            return null;
        }
        Ast.FnDef reached = table.reached(name.reaches());
        return reached == null || reached.body() == null ? null : reached.writtenBody();
    }

    /** The next number this pass has for the body it is writing into. */
    private int next() {
        return written.merge(writing.into(), 1, Integer::sum) - 1;
    }

    /** How the source wrote an expression that is a name or a chain of field reads off one, or null
     *  where it wrote something with no spelling of its own — a call's result, a lambda. */
    private static String spelling(Ast.Expr e) {
        return switch (e) {
            case Ast.Var v -> v.name();
            case Ast.FieldAccess fa -> {
                String target = spelling(fa.target());
                yield target == null ? null : target + "." + fa.field();
            }
            default -> null;
        };
    }

    /** Rewrites every helper call in {@code e} to its inlined body, into the body this writing names.
     * Private, because there is no body to write into until a writing says which, and the writings
     * are started above. */
    private Ast.Expr inline(Ast.Expr e) {
        return switch (e) {
            // Applying something other than a name. The applied expression is bound first and the
            // application reads the binding, which is the shape every reader downstream already has
            // — and which says outright what the order is: the function is worked out once, before
            // any argument, and the binding is what is applied.
            case Ast.Apply raw when !raw.appliesAName() -> {
                Ast.Binder f = writing.binders().binder("$fn" + next(), raw.function().pos());
                // What the application reaches is the binding, and what a report about it quotes is
                // what the author wrote — a field read applied (`deps.count(x)`) has a spelling, and
                // quoting the binding would name `$fn0`, which is nowhere in the source. The two are
                // separate slots: the binding is in the callee position, the spelling beside it.
                yield inline(new Ast.LetIn(f, raw.function(), null, false, null,
                        new Ast.Apply(Ast.Var.respelled(f.name(),
                                new ValueName.Local(f.name(), f.id()),
                                new ReachName.Bare(f.name()), raw.function().pos(),
                                raw.function().region()),
                                raw.args(), raw.origin(), spelling(raw.function()), raw.pos(),
                                raw.region()),
                        raw.pos(), raw.region()));
            }
            case Ast.Apply rawCall -> expandCall(rawCall);
            case Ast.FieldAccess fa -> fa.withTarget(inline(fa.target()));
            case Ast.Binary bin -> new Ast.Binary(bin.op(), inline(bin.left()), inline(bin.right()),
                    bin.origin(), bin.pos(), bin.region());
            case Ast.Neg neg -> new Ast.Neg(inline(neg.operand()), neg.pos(), neg.region());
            case Ast.NewData nd -> newData(nd);
            case Ast.Match m -> {
                List<Ast.Case> cases = new ArrayList<>();
                for (Ast.Case c : m.cases()) {
                    cases.add(new Ast.Case(c.caseTypes(), c.binding(), inline(c.body()), c.unwrapAsserts(), c.pos()));
                }
                yield new Ast.Match(inline(m.scrutinee()), cases, m.origin(), m.pos(), m.region());
            }
            case Ast.If iff -> new Ast.If(inline(iff.cond()), inline(iff.then()), inline(iff.els()),
                    iff.origin(), iff.pos(), iff.region());
            case Ast.IfConstructed ic -> new Ast.IfConstructed(inline(ic.construct()), ic.binder(),
                    inline(ic.then()), Ast.mapArms(ic.els(), this::inline), ic.origin(), ic.pos(),
                    ic.region());
            // Already expanded. Its body may still hold calls of its own — a helper whose callee was
            // not in the table when this ran the first time — so it is walked like any other.
            case Ast.Expansion ex -> {
                List<Ast.Bound> bound = new ArrayList<>();
                for (Ast.Bound b : ex.bound()) {
                    bound.add(new Ast.Bound(b.binder(), b.declaredType(), inline(b.value())));
                }
                List<Ast.Given> given = new ArrayList<>();
                for (Ast.Given g : ex.given()) {
                    given.add(new Ast.Given(g.declaredType(), inline(g.value()), g.applied(),
                            g.arrivesAs()));
                }
                yield new Ast.Expansion(ex.callee(), ex.application(), bound, given,
                        ex.declaredReturn(), inline(ex.body()), ex.pos(), ex.region());
            }
            case Ast.LetIn li -> {
                // What the value turns out to be is what decides this, so it is worked out first: a
                // lambda the author wrote and a named function read as a value are the same block by
                // the time either gets here, and a `let` should not tell them apart.
                Ast.Expr value = inline(li.value());
                // A binding that holds a function, read into another binding: the second names the
                // same function, so it is registered under it. Nothing is copied — what a name means
                // is what it was given, and here it was given a binding.
                Ast.FnDef aliased = value instanceof Ast.Var v ? expands(v.denotes(), v.reaches()) : null;
                if (aliased != null) {
                    BindingId alias = li.binder().id();
                    writing.scopedLambdas().put(alias, new ScopedLambda(aliased));
                    Ast.Expr aliasBody = inline(li.body());
                    writing.scopedLambdas().remove(alias);
                    yield references(aliasBody, alias)
                            ? new Ast.LetIn(li.binder(), value, li.declaredType(), li.annotated(),
                                    li.opens(), aliasBody, li.pos(), li.region())
                            : aliasBody;
                }
                if (!(value instanceof Ast.Block lambda)) {
                    yield new Ast.LetIn(li.binder(), value, li.declaredType(), li.annotated(),
                            li.opens(), inline(li.body()), li.pos(), li.region());
                }
                // a function bound to a local: registered under that binding, so each application of
                // it in the body expands inline (β-reduction) exactly as a named helper does. Its
                // parameters are untyped, so their types flow in from the arguments at expansion. No
                // runtime closure is built as long as it does not escape.
                //
                // It cannot reach itself: a `let` does not bind its own name in its value (spec
                // 16.1), so a name inside spelled like it is whatever it was outside, and expansion
                // follows what a name denotes rather than how it is spelled.
                List<Ast.FnParam> params = new ArrayList<>();
                for (Ast.Binder p : lambda.params()) {
                    params.add(new Ast.FnParam(p, null));
                }
                BindingId bound = li.binder().id();
                writing.scopedLambdas().put(bound, new ScopedLambda(
                        Ast.FnDef.lambda(li.name(), params, null,
                                new Ast.FnBody.Written(lambda.body()), li.pos())));
                Ast.Expr body = inline(li.body());
                writing.scopedLambdas().remove(bound);
                // if the binding is still read, the function was used as a value, not just applied —
                // it escapes, which needs a runtime closure. Keep the binding so the check that
                // reports an escaping block sees it.
                yield references(body, bound)
                        ? new Ast.LetIn(li.binder(), lambda, li.declaredType(), li.annotated(),
                                li.opens(), body, li.pos(), li.region())
                        : body;
            }
            case Ast.ListLit lit -> new Ast.ListLit(inlineList(lit.elements()), lit.pos(), lit.region());
            case Ast.Tuple tup -> new Ast.Tuple(inlineList(tup.elements()), tup.pos(), tup.region());
            case Ast.TupleGet tg -> new Ast.TupleGet(inline(tg.tuple()), tg.index(), tg.arity(), tg.pos(),
                    tg.region());
            case Ast.ListComp comp -> new Ast.ListComp(inline(comp.element()), inlineList(comp.guards()),
                    comp.origin(), comp.pos(), comp.region());
            case Ast.Block block -> new Ast.Block(block.params(), inline(block.body()), block.pos(),
                    block.region());
            case Ast.IntLit _ -> e;
            case Ast.DecimalLit _ -> e;
            case Ast.StringLit _ -> e;
            case Ast.BoolLit _ -> e;
            case Ast.Unreachable _ -> e;
            case Ast.Var v -> valueOf(v);
        };
    }

    /**
     * One call of a name, with the callee's body in place of it where a body stands behind the name.
     *
     * <p>Not every call has one. A builtin, an injected behavior, a function-typed parameter and a
     * recursive helper are all applied by something other than an expansion, so the call stays a call
     * and only its arguments are expanded. What is left — a non-recursive helper, a value that is a
     * function, a lambda a binding holds — becomes an {@link Ast.Expansion}: one node, because the
     * callee's signature is one statement and this call decides its variables once.
     */
    private Ast.Expr expandCall(Ast.Apply rawCall) {
        if (rawCall.function() instanceof Ast.Var.Unanswered) {
            // The callee names nothing, which was reported where it is written. No body stands
            // behind it, no library sugar reaches for it, and no parameter list holds its arguments
            // against anything — so the call stays as it is and only its arguments are expanded.
            List<Ast.Expr> args = new ArrayList<>();
            for (Ast.Expr a : rawCall.args()) {
                args.add(inline(a));
            }
            return rawCall.withArgs(args);
        }
        checkFunctionArgumentPlacement(rawCall);
        Ast.Apply call = desugarNamedBlock(desugar(rawCall));
        List<Ast.Expr> args = new ArrayList<>();
        for (Ast.Expr a : call.args()) {
            args.add(inline(a));
        }
        Ast.FnDef helper = appliedHelper(call);
        // a recursive helper is reached by the name it is declared under; a lambda a binding
        // holds is not one, whatever it is called
        boolean standing = !(call.denotes() instanceof ValueName.Local)
                && graph.recurses(call.reaches());
        if (helper == null || standing) {
            // builtin, injected behavior, a function-typed parameter, or a recursive helper —
            // a recursive helper is lowered to a method, so its call stays a Call (spec §fn-declaration);
            // only its args inline.
            return call.withArgs(forwardDependencies(helper, args));
        }
        // A declaration written with no parameter list is a value ([#fn-declaration]), so
        // applying it applies whatever function that value is — not the declaration, which
        // takes nothing. The value is substituted and the arguments are applied to it.
        if (helper.params().isEmpty() && !args.isEmpty()
                && call.function() instanceof Ast.Var named) {
            return inline(new Ast.Apply(valueOf(named), args, call.origin(), call.pos(),
                    call.region()));
        }
        if (args.size() != helper.params().size()) {
            throw wrongArity(call, helper, args.size());
        }
        // Everything this expansion writes belongs to it: the bindings its arguments become,
        // the one a lambda given to a function parameter is registered under, the one its
        // declared return is carried on, and every binding copied out of the callee's body.
        // One minter, so no two of them are the same binding, and a reader can ask of any of
        // them which call it came from.
        BindingOwner mine = new BindingOwner.Expansion(writing.into(), call.denotes(), next());
        Ast.Binders ours = new Ast.Binders(mine);
        // What the callee's signature leaves open, this call decides. Its variables are
        // instantiated once, here, over the whole signature at once — so a variable it wrote
        // in two of its parameters is one variable in what this expansion writes, and two
        // calls of it decide separately. Splitting the signature into a binding per parameter
        // is what would otherwise lose that: each binding's type would be read on its own,
        // and nothing left afterwards says the two came from one application.
        Map<String, Type> applied = instantiation(helper, mine);
        Arguments arguments = bindArguments(rawCall, call, helper, args, applied, ours);
        // a prelude helper's body is stamped with the call site, so errors inside it point at
        // the user's call, not at the shipped source of souther.*
        Renaming renaming = new Renaming(arguments.subst(), new Copy(helper.writtenBody(), ours),
                keepsItsPositions(call) ? null : call.pos(),
                keepsItsPositions(call) ? null : call.region());
        Ast.Expr body = inline(rename(helper.writtenBody(), renaming));   // expand nested helpers too
        List<Ast.Bound> bound = new ArrayList<>(arguments.bound());
        // A scoped lambda the body still names was passed rather than applied, so nothing
        // reduced it and the name would stand for nothing. It is bound to what it names, which
        // is what a lambda given a name is anywhere else.
        arguments.unreduced().forEach((id, lambda) -> {
            if (references(body, id)) {
                bound.add(lambda);
            }
        });
        arguments.unreduced().keySet().forEach(writing.scopedLambdas()::remove);
        return new Ast.Expansion(call.denotes(), mine, bound, arguments.given(),
                instantiated(helper.declaredReturn(), applied), body, call.pos(), call.region());
    }

    /**
     * A call written with a different number of arguments than the callee takes, named against
     * whichever of the two the author wrote.
     *
     * <p>A lambda given to a function parameter is inlined under a synthetic name, so a report that
     * quoted the callee would quote a name nowhere in the source. Where the callee is one of those,
     * the parameter count is reported against the lambda instead.
     */
    private CompileException wrongArity(Ast.Apply call, Ast.FnDef helper, int given) {
        ScopedLambda applied = call.denotes() instanceof ValueName.Local local
                ? writing.scopedLambdas().get(local.id()) : null;
        LambdaOrigin origin = applied == null ? null : applied.origin();
        if (origin != null) {
            return CompileException.of(Diagnostic.at(origin.pos())
                    .say(new HelperMessage.TheBlockTakesAnotherNumberOfArguments(origin.param(),
                            origin.owner(), String.valueOf(given),
                            String.valueOf(helper.params().size())))
                    .build());
        }
        return CompileException.of(Diagnostic.at(call.appliedAt())
                .say(new HelperMessage.CalledWithAnotherNumberOfArguments(helper.name(),
                        String.valueOf(helper.params().size()), String.valueOf(given)))
                .build());
    }

    /**
     * What one call's arguments become where the callee's body is spliced in.
     *
     * <p>A value argument becomes a binding the body reads by name; a function argument becomes
     * neither — it leaves no binding, so what the signature said about it is held in {@code given}
     * and nowhere else. {@code subst} answers the callee's parameters in both cases, so the copied
     * body reads one thing per parameter however the parameter arrives.
     *
     * <p>{@code unreduced} holds the lambdas registered under a fresh binding, each with the binding
     * a {@code let} would hold it in. They are the ones this expansion may not reduce away — a
     * representation that keeps a call standing keeps the application inside it — so the binding is
     * built ahead and used only for the ones the body still names afterwards. Being the keys of that
     * map is also what says which registrations this call has to drop when it is done.
     */
    private record Arguments(Map<BindingId, Substituted> subst, List<Ast.Bound> bound,
                             List<Ast.Given> given, Map<BindingId, Ast.Bound> unreduced) {}

    /**
     * Binds one call's arguments against the callee's parameters, this call's variables written in.
     *
     * <p>{@code rawCall} is the call as the author wrote it, which is what a report about an argument
     * quotes; {@code call} is what it desugared to, which is what the expansion is built from.
     */
    private Arguments bindArguments(Ast.Apply rawCall, Ast.Apply call, Ast.FnDef helper,
                                    List<Ast.Expr> args, Map<String, Type> applied,
                                    Ast.Binders ours) {
        // what stands in the body for each of the callee's parameters: the name it is written
        // as and what that name resolved to at the call site, so the expansion carries the
        // argument's own answer rather than deciding one for it
        Map<BindingId, Substituted> subst = new HashMap<>();
        Map<BindingId, Ast.Bound> unreduced = new LinkedHashMap<>();
        List<Ast.Bound> bound = new ArrayList<>();
        List<Ast.Given> given = new ArrayList<>();
        for (int i = 0; i < helper.params().size(); i++) {
            Ast.FnParam p = helper.params().get(i);
            Ast.Expr arg = args.get(i);
            if (p.type() != null && p.type().asFn() != null) {
                // a function argument is not a value, so it cannot be bound to a let. A named
                // function is substituted directly (f(x) becomes inc(x)); a lambda is
                // registered under a fresh name as a scoped helper, so each application of the
                // parameter β-reduces to the lambda's body, as a let-bound lambda does (spec §blocks).
                // Asked of the callee as written, not of what it expanded to: applying a
                // function parameter is what removes it, because the application β-reduces
                // to the lambda's body, so the expansion holds no reference either way.
                given.add(new Ast.Given(instantiated(p.type(), applied), arg,
                        references(helper.writtenBody(), p.binder().id()), arrivesAs(arg)));
                Ast.FnType declares = declaredFn(p.type(), applied);
                if (arg instanceof Ast.Var.Denoting fnName) {
                    // A name handed to a function parameter is substituted through: what
                    // applies it applies what it stands for. What it stands for is declared
                    // somewhere — a helper's own parameter, a binding, a function an
                    // enclosing call gave — and that declaration is carried on the boundary,
                    // so the two are read against each other without either being re-typed.
                    subst.put(p.binder().id(), new Substituted(fnName.name(), fnName.denotes()));
                } else if (arg instanceof Ast.Block lambda) {
                    Ast.Binder f = ours.binder("$" + p.name(), lambda.pos());
                    subst.put(p.binder().id(), Substituted.of(f));
                    // The lambda is registered under what the callee declared of the
                    // parameter it was given to, this application's variables written in. So
                    // where the callee applies it, that application expands like any other
                    // call and is read against the signature there — in the one place the
                    // types this application decided are in force. Registering it bare is
                    // what used to throw the signature away at the point it was reduced,
                    // leaving nothing between the caller's function and what was declared of
                    // it (issues #318, #320).
                    List<Ast.FnParam> lparams = new ArrayList<>();
                    for (int lp = 0; lp < lambda.params().size(); lp++) {
                        lparams.add(new Ast.FnParam(lambda.params().get(lp),
                                declares == null || lp >= declares.params().size() ? null
                                        : declares.params().get(lp)));
                    }
                    // the lambda's body is caller code, so it is not renamed by this helper's
                    // substitution — only the enclosing helper body is.
                    writing.scopedLambdas().put(f.id(), new ScopedLambda(
                            Ast.FnDef.lambda(f.name(), lparams,
                                    declares == null ? null : declares.result(),
                                    new Ast.FnBody.Written(lambda.body()), lambda.pos()),
                            new LambdaOrigin(p.name(), helper.name(), lambda.pos())));
                    unreduced.put(f.id(),
                            new Ast.Bound(f, instantiated(p.type(), applied), lambda));
                } else {
                    throw notAFunction(rawCall, p, i, arg);
                }
            } else {
                // the binding the argument is bound to; the reads of the parameter inside the
                // body are answered with it, so a read says which binding it is rather than
                // where it happens to be written
                Ast.Binder f = ours.binder(p.name(), call.pos());
                subst.put(p.binder().id(), Substituted.of(f));
                // carry the parameter's declared type onto the binding, so a value known to
                // be a sum (an annotated `s: S`) is not narrowed to the argument's specific
                // case when the body is re-checked inline — a `match s` inside still sees S.
                bound.add(new Ast.Bound(f, instantiated(p.type(), applied), arg));
            }
        }
        return new Arguments(subst, bound, given, unreduced);
    }

    /**
     * A value written where a function goes — the argument-order mistake made with a named helper
     * rather than a lambda. Named against the call as written, with the declared order.
     */
    private CompileException notAFunction(Ast.Apply rawCall, Ast.FnParam p, int index, Ast.Expr arg) {
        List<Ast.FnParam> written = declaredParams(rawCall);
        String shape = written == null ? null : written.stream()
                .map(Ast.FnParam::name)
                .collect(java.util.stream.Collectors.joining(", "));
        Diagnostic.Builder d = Diagnostic.at(arg.pos())
                .say(new HelperMessage.ThisArgumentTakesAFunction(rawCall.written(),
                        String.valueOf(index + 1), p.name()));
        if (shape != null) {
            d.hint(new HelperMessage.WriteTheCallThisWay(rawCall.written(), shape));
        }
        return CompileException.of(d.build());
    }

    /**
     * {@code function} as the function value it names: a block taking as many parameters as the
     * function takes and applying it to them. The same value the author would get by spelling the
     * lambda, so nothing downstream has to know which of the two was written.
     *
     * <p>{@code binderName} names the block's parameters, given the index of each. A source
     * identifier never starts with {@code $}, so a name from any of the callers cannot capture a
     * local of the body it is written into.
     */
    private Ast.Block etaExpand(Ast.Var function, int arity, IntFunction<String> binderName) {
        List<Ast.Binder> params = new ArrayList<>();
        List<Ast.Expr> args = new ArrayList<>();
        for (int i = 0; i < arity; i++) {
            Ast.Binder p = writing.binders().binder(binderName.apply(i), function.pos());
            params.add(p);
            args.add(Ast.Var.local(p, function.pos()));
        }
        // The block and the application in it are this pass's: what the author wrote there is a
        // name, and these are the parameters and the call it stands for.
        return new Ast.Block(params,
                new Ast.Apply(function, args, ConstructionOrigin.own(), function.pos(), null),
                function.pos(), null);
    }

    /**
     * How many inputs the declaration {@code v} reaches takes, where that declaration is one a name
     * written in value position stands for — and empty where the name reaches no such declaration.
     *
     * <p>This asks the declaration and nothing else: not whether the implementation is a Souther
     * body, a kernel or a Java one, which is what is on the other side of the name and not the
     * name's business. A helper, a library function and a behavior differ in what stands behind
     * them and not in what reification needs, which is how many arguments the block it becomes
     * takes.
     *
     * <p>Empty covers a declaration taking nothing and every name that stands for no declaration at
     * all: a binding, a construction, a library name the library does not declare, and a behavior
     * this body may not name. Each of those is left as it was written and reported where it is
     * used. A declaration taking nothing has no function value to become rather than one this
     * declines to make: a {@code let} with no parameter list is a value and is written without
     * {@code ()}, and there is no block taking no parameter to expand it to.
     */
    private OptionalInt declarationArity(Ast.Var v) {
        if (!(v instanceof Ast.Var.Denoting)) {
            return OptionalInt.empty();   // it stands for no declaration to take anything
        }
        int arity = switch (v.denotes()) {
            case ValueName.Stdlib lib -> {
                Prelude.PreludeEntry entry = Prelude.entry(lib.qualified());
                Ast.FnDef declared = entry == null ? null : entry.declaration();
                yield declared == null ? 0 : declared.params().size();
            }
            case ValueName.Helper _ -> {
                Ast.FnDef declared = table.reached(v.reaches());
                yield declared == null || declared.body() == null ? 0 : declared.params().size();
            }
            // A behavior's name handed over is the behavior: the block applies the behavior, so the
            // emitted code goes through the behavior's class and not through the `let` that
            // implements it. Only the ones a body may name are here — a behavior with a requirement
            // is a binding by the time it can be written.
            case ValueName.Behavior b -> callableBehaviors.getOrDefault(b.name(), 0);
            // A binding holds whatever it was given; a construction, a checker built-in and a name
            // that denotes nothing stand for no declaration at all.
            case ValueName.Local _, ValueName.OfType _, ValueName.Builtin _ -> 0;
            case null -> 0;
        };
        return arity == 0 ? OptionalInt.empty() : OptionalInt.of(arity);
    }

    /**
     * A name written where a value goes, as the value it stands for.
     *
     * <p>A name that reaches a declaration taking arguments is the function it names, written out.
     * A recursive helper is written out too — the call inside stays the call it has to be.
     *
     * <p>A name that denotes a value — a {@code let} written with no parameter list — is expanded to
     * the expression it was defined as. A value is not module state: its body is elaborated where it
     * was declared and substituted at each reference, so nothing is held between them and there is
     * no order in which the module's values come into being. A recursive value is left alone here;
     * the recursion check reports it under its own name.
     *
     * <p>Anything else — a binding, a unit data — is the name itself.
     */
    private Ast.Expr valueOf(Ast.Var v) {
        OptionalInt arity = declarationArity(v);
        if (arity.isPresent()) {
            int k = next();
            return inline(etaExpand(v, arity.getAsInt(), i -> "$v" + k + "_" + i));
        }
        if (!(v instanceof Ast.Var.Denoting) || !(v.denotes() instanceof ValueName.Helper)) {
            return v;
        }
        Ast.FnDef value = table.reached(v.reaches());
        // Asked with the name the table was asked with. The graph is keyed as the table is, and a
        // spelling agrees with that key only where a pass has already written it out qualified.
        if (value == null || value.body() == null || graph.recurses(v.reaches())) {
            return v;
        }
        Ast.Expr settled = settled(v);
        return settled != null ? settled : substituted(v.reaches(), value.writtenBody());
    }

    /**
     * What {@code v} stands for where this expansion was told the value's own answer, or null where
     * it was not and the body has to be copied.
     *
     * <p>Two answers, because two things read a substituted value. What it types as is read by the
     * check, and a reference standing under the settled type says it. What it is a constant of is
     * read by everything that asks whether an expression is known at compile time — a
     * {@code String.matches} pattern, the argument a construction proves its invariant against —
     * and those fold a tree rather than resolve a name ({@link ConstEval}), so a constant is written
     * out as the literal it folded to and they go on reading a literal. Where the value is neither
     * — a construction, a collection, anything a fold does not reach — the reference stands and the
     * check reads its type.
     *
     * <p>The literal is written at the reference. A value is substituted at each of its references
     * (ADR-0072), so what stands there is this reference's, and a report about it belongs where the
     * name was written rather than in the body it came from.
     */
    private Ast.Expr settled(Ast.Var v) {
        Type type = settledValues.valueKept(v.denotes());
        if (type == null) {
            return null;
        }
        Object constant = settledConstants.apply(v.denotes());
        return constant == null ? v : literal(constant, v.pos());
    }

    /** {@code constant} as the expression a fold would read it back out of, or null for a value no
     * literal spells. */
    private static Ast.Expr literal(Object constant, SourcePos pos) {
        return switch (constant) {
            // A value the fold arrived at, which no run of characters in the file spells.
            case Long i -> new Ast.IntLit(i, pos, null);
            case java.math.BigDecimal d -> new Ast.DecimalLit(d, pos, null);
            case String s -> new Ast.StringLit(s, pos, null);
            case Boolean b -> new Ast.BoolLit(b, pos, null);
            default -> null;
        };
    }

    /**
     * The body of the value {@code reached} stands for, expanded here — and a refusal where this
     * expansion is already substituting that value.
     *
     * <p>Substituting a value into itself has no end, so an expansion that reached one would descend
     * until the stack ran out. Which modules that can happen to is answered before anything expands a
     * body of one, and it is {@link ValueCycles} that answers it and says so to the author. This is
     * not that rule said twice: it is about this algorithm rather than about the module, and what it
     * gives is that expanding is bounded whatever it is handed. A caller that reached here with a
     * module the answer above would have refused gets a failure naming the value, rather than a stack
     * that ran out and a report about an expression nesting too deeply.
     *
     * <p>What it holds is the path and not what it has seen: a value named twice in one body is
     * substituted twice, side by side, and only one inside the other is re-entry.
     *
     * <p>The path is also what says whose job the mark is. What a value carried is written over the
     * whole expansion once it is whole, by the substitution no other substitution is inside — the
     * outermost one holds every subtree the ones under it produced, and the mark is a flag, so
     * writing it there says of each node what writing it at every level said. Written at every
     * level it is written over each subtree once per level that subtree is under, which is the
     * depth of a chain of values times its length. The walk allocates nothing — rebuilding an
     * expression hands back what it was given where nothing changed — so what it costs is the
     * walking, and nothing downstream of it can see that it ran twice.
     */
    private Ast.Expr substituted(String reached, Ast.Expr body) {
        if (!substituting.add(reached)) {
            throw new ExpansionCycle("`" + reached + "` is substituted into itself ("
                    + String.join(" -> ", substituting) + " -> " + reached + "), and a module whose"
                    + " values are not well founded is refused before a body of it is expanded");
        }
        try {
            Ast.Expr expanded = inline(body);
            return substituting.size() == 1 ? HelperNames.carriedByValue(expanded) : expanded;
        } finally {
            substituting.remove(reached);
        }
    }

    /**
     * A construction, with any spread of a value bound first.
     *
     * <p>A spread names a value the way any other position does, but it holds a name rather than an
     * expression, so the value cannot be substituted in place. It is bound to a fresh {@code $}-name
     * ahead of the construction and the spread copies that binding — the shape a spread of a local
     * already has, so nothing downstream learns a new one.
     */
    private Ast.Expr newData(Ast.NewData nd) {
        List<Ast.Binder> bound = new ArrayList<>();
        List<Ast.Expr> values = new ArrayList<>();
        List<Ast.Var> spreads = new ArrayList<>();
        for (Ast.Var spread : nd.spreads()) {
            Ast.FnDef value = valueSpread(spread);
            if (value == null) {
                spreads.add(spread);
                continue;
            }
            Ast.Binder name = writing.binders().binder("$s" + next() + "_" + spread.bare(), spread.pos());
            bound.add(name);
            values.add(substituted(spread.name(), value.writtenBody()));
            spreads.add(Ast.Var.local(name, spread.pos()));
        }
        Ast.Expr built = new Ast.NewData(nd.typeName(), inlineInits(nd.inits()), spreads,
                nd.origin(), nd.pos(), nd.region());
        // The bindings a spread of a value becomes stand where the construction stands.
        for (int i = bound.size() - 1; i >= 0; i--) {
            built = new Ast.LetIn(bound.get(i), values.get(i), null, false, null, built, nd.pos(),
                    nd.region());
        }
        return built;
    }

    private List<Ast.Expr> inlineList(List<Ast.Expr> es) {
        List<Ast.Expr> out = new ArrayList<>();
        for (Ast.Expr e : es) {
            out.add(inline(e));
        }
        return out;
    }

    private List<Ast.FieldInit> inlineInits(List<Ast.FieldInit> inits) {
        List<Ast.FieldInit> out = new ArrayList<>();
        for (Ast.FieldInit i : inits) {
            out.add(i.withValue(inline(i.value())));
        }
        return out;
    }

    /**
     * A helper fn passed to {@code fold} by name is sugar for a block that wraps a call:
     * {@code List.fold(step, seed, xs)} with a named {@code step} becomes
     * {@code List.fold(($b0, $b1) -> step($b0, $b1), seed, xs)} (spec §blocks, "名前で直接渡す。同じこと").
     * The generated block has one parameter per helper parameter, so a later arity check against
     * {@code fold} (it wants two) still applies. The block is then expanded inline like any other
     * helper call. Only {@code fold} needs this — map/filter/all/any are helpers whose function
     * parameter the inliner binds directly (see {@link #inline}).
     */
    private Ast.Apply desugarNamedBlock(Ast.Apply call) {
        if (!(call.function() instanceof Ast.Var.Denoting)) {
            return call;   // it reaches nothing, so it is no named block to desugar
        }
        Integer idx = BLOCK_ARG.get(call.reaches());
        if (idx == null || idx >= call.args().size()
                || !(call.args().get(idx) instanceof Ast.Var.Denoting v)) {
            return call;
        }
        Ast.FnDef helper = expands(v.denotes(), v.reaches());
        if (helper == null) {
            return call;   // a bare name that stands for no body is left for the type checker to report
        }
        int k = next();
        Ast.Block block = etaExpand(v, helper.params().size(), i -> "$b" + k + "_" + i);
        List<Ast.Expr> args = new ArrayList<>(call.args());
        args.set(idx, block);
        return call.withArgs(args);
    }

    /**
     * One copy of a body, and the bindings it has of its own.
     *
     * <p>A body spliced into a caller brings its bindings with it, and a second splice brings them
     * again — so each copy owns them rather than the definition they were written in. A binding met
     * in the copy is answered with the copy's, and every name that read it in the original reads the
     * copy's too; a name the substitution answers is the caller's and is left alone.
     */
    private static final class Copy {

        private final Map<BindingId, BindingId> mine = new HashMap<>();

        /**
         * Every binding the body introduces, given one of this copy's, before any of it is written.
         *
         * <p>Assigned in one pass so that a binder and the names that read it are moved together
         * whatever order the copy is written in: a read met before its binder would otherwise be
         * left on the original while the binder moved, and the two would no longer be one binding.
         */
        private Copy(Ast.Expr body, Ast.Binders binders) {
            eachBinder(body, binder ->
                    mine.put(binder.id(), binders.binder(binder.name(), binder.pos()).id()));
        }

        /** This copy's binder for one the body has. The copy is this pass's writing, however much
         * it reads like the body it was taken from, so it claims no name position: the place the
         * author wrote that name is the original binding's and stays with it. */
        Ast.Binder of(Ast.Binder binder) {
            return new Ast.Binder.Bound(WrittenName.synthetic(binder.name(), binder.pos()),
                    mine.get(binder.id()), binder.pos());
        }

        /** The same, for a name that reads one. A name bound outside the body — a parameter, which
         * the substitution answers — is not this copy's to move. */
        ValueName of(ValueName denotes) {
            if (!(denotes instanceof ValueName.Local local)) {
                return denotes;
            }
            BindingId here = mine.get(local.id());
            return here == null ? denotes : new ValueName.Local(local.name(), here);
        }
    }

    /**
     * What stands in the body for one of the callee's parameters: the name it is written as, and what
     * that name means.
     *
     * <p>One fact and one value. Written as two tables it was possible to put a name into one and no
     * answer into the other, so a read of the name had to be checked at run time against the table
     * that was supposed to answer it — and the two could only be made to agree by a check, never by
     * construction. Here the name and its answer are put in together or not at all.
     */
    private record Substituted(String name, ValueName denotes) {

        /** The binding an expansion made, read as the name the body will read. */
        static Substituted of(Ast.Binder binder) {
            return new Substituted(binder.name(), new ValueName.Local(binder.name(), binder.id()));
        }

        /** A binding is reached where it is bound, so its own name is the whole of it. */
        ReachName reachedAs() {
            return new ReachName.Bare(name);
        }
    }

    /**
     * What one expansion rewrites as it copies the callee's body: which parameter reads become which
     * names, which of the body's own bindings become which, and what position the copy carries.
     *
     * <p>The three are fixed for the whole copy and none of them changes as the walk descends, so they
     * travel together rather than as three parameters threaded through every node kind.
     */
    private record Renaming(Map<BindingId, Substituted> subst, Copy copy, SourcePos at,
                            Region over) {

        /** What {@code denotes} stands for in this copy, or null where nothing does — an inner binder
         * that happens to spell a parameter's name is a different binding with a different id, so a
         * reference under it is not in the substitution and is left to {@link #copy}. */
        Substituted substituted(ValueName denotes) {
            return denotes instanceof ValueName.Local local ? subst.get(local.id()) : null;
        }

        /**
         * The position a rebuilt node carries: the call site where the copy is stamped with it, and
         * otherwise the node's own.
         *
         * <p>A prelude helper is copied with the call site stamped over it, so a type error inside its
         * body points at the user's call — {@code filter(xs, x -> x * 2)} — rather than at a line of
         * {@code souther.list} the user never wrote. A module-own helper, and a lambda given to a fn
         * parameter, keep the positions their bodies have ({@link HelperInliner#keepsItsPositions}).
         * The caller's argument expressions are spliced in separately and keep their own either way.
         */
        SourcePos at(SourcePos own) {
            return at != null ? at : own;
        }

        /** Whether this copy is being stamped with the call site rather than keeping its own. */
        boolean stamps() {
            return at != null;
        }

        /**
         * The stretch of source a rebuilt node is written over: the call's where the copy is stamped
         * with it, and otherwise the node's own.
         *
         * <p>The same rule as {@link #at}, over the same nodes, because a copy stamped with the call
         * site is written where the call is — all of it, not one point of it. A node that took the
         * call's position and kept the callee's extent would say a report is about characters of one
         * file at a line of another.
         */
        Region over(Region own) {
            return at != null ? over : own;
        }
    }

    /**
     * Every binder written inside {@code e}, itself included where {@code e} is one.
     *
     * <p>The node kinds that introduce a binding are named here and nowhere else in this pass, so a
     * kind added later is added once. The walk into the children is {@link Ast#forEachChild}, which
     * is exhaustive over the expression kinds, so a new one cannot be missed.
     */
    private static void eachBinder(Ast.Expr e, java.util.function.Consumer<Ast.Binder> f) {
        switch (e) {
            case Ast.LetIn li -> f.accept(li.binder());
            // What was given to a function parameter is walked here although it is not a slot: it is
            // not code the expansion runs — the body holds it wherever the callee applies it — but a
            // copy of this body has to move its binders along with the rest, or the copy would name
            // a binding that stayed behind.
            case Ast.Expansion ex -> {
                ex.bound().forEach(b -> f.accept(b.binder()));
                ex.given().forEach(g -> eachBinder(g.value(), f));
            }
            case Ast.Block b -> b.params().forEach(f);
            case Ast.IfConstructed ic -> f.accept(ic.binder());
            case Ast.Match m -> {
                for (Ast.Case c : m.cases()) {
                    if (c.binding() != null) {
                        f.accept(c.binding());
                    }
                }
            }
            default -> { }
        }
        forEachChild(e, child -> eachBinder(child, f));
    }

    /**
     * Renaming of the helper's parameter references, matched by {@code BindingId}. An inner binder
     * that happens to spell a parameter's name is a different binding with a different id, so a
     * reference under it names that binding, is not in the substitution, and is left untouched —
     * capture avoidance is the resolver's answer, not a rule of this walk.
     *
     * <p>A callee is renamed as the subexpression it is, so applying a name asks the same question a
     * read of it asks and can only get the same answer: an application {@code f(x)} of a parameter
     * becomes a call to what the parameter was bound to — a function argument, or a value whose type
     * the application is then checked against. There is no separate rule for the callee position to
     * fall out of step with. A spelling that means something else — a builtin, a helper — was
     * resolved to that before renaming and is not a {@code ValueName.Local}, so it is left alone.
     *
     * <p>What each rebuilt node's position becomes is {@link Renaming#at}'s to say, and it says it
     * once for every node kind here.
     */
    private Ast.Expr rename(Ast.Expr e, Renaming renaming) {
        return switch (e) {
            case Ast.Var v -> renameVar(v, renaming);
            // The field's occurrence goes the way the initialiser's does below: it is in the callee's
            // file, so a copy being read against the caller's does not carry it. A report about the
            // read is anchored at the field, so keeping it would send one to the callee's source
            // while everything around it points at the call.
            case Ast.FieldAccess fa -> renaming.stamps()
                    ? Ast.FieldAccess.restamped(rename(fa.target(), renaming), fa.field(),
                            renaming.at(fa.pos()), renaming.over(fa.region()))
                    : fa.withTarget(rename(fa.target(), renaming));
            // the callee is renamed as the expression it is, like every other subexpression. A name
            // applied is an `Ast.Var` held here, so it goes through the arm above and is substituted
            // exactly as a read of it would be — the position cannot ask a different question.
            case Ast.Apply call -> new Ast.Apply(
                    rename(call.function(), renaming),
                    renameList(call.args(), renaming),
                    call.origin(), call.appliedAs(), renaming.at(call.pos()),
                    renaming.over(call.region()));
            case Ast.Binary bin -> new Ast.Binary(bin.op(), rename(bin.left(), renaming),
                    rename(bin.right(), renaming), bin.origin(), renaming.at(bin.pos()),
                    renaming.over(bin.region()));
            case Ast.Neg neg -> new Ast.Neg(rename(neg.operand(), renaming), renaming.at(neg.pos()),
                    renaming.over(neg.region()));
            case Ast.NewData nd -> {
                List<Ast.FieldInit> inits = new ArrayList<>();
                for (Ast.FieldInit i : nd.inits()) {
                    // A copy stamped with the call site is being read against the caller's file,
                    // so the field's occurrence — which is in the callee's — does not come with it.
                    Ast.Expr filled = rename(i.value(), renaming);
                    inits.add(renaming.stamps()
                            ? new Ast.FieldInit(i.name(), filled, renaming.at(i.pos()))
                            : i.withValue(filled));
                }
                // `..param` copies the renamed binding: a name slot asks what a name asks
                List<Ast.Var> spreads = new ArrayList<>();
                for (Ast.Var s : nd.spreads()) {
                    spreads.add(renameVar(s, renaming));
                }
                yield new Ast.NewData(nd.typeName(), inits, spreads, nd.origin(), renaming.at(nd.pos()),
                        renaming.over(nd.region()));
            }
            case Ast.Match m -> {
                List<Ast.Case> cases = new ArrayList<>();
                for (Ast.Case c : m.cases()) {
                    cases.add(new Ast.Case(c.caseTypes(),
                            c.binding() == null ? null : renaming.copy().of(c.binding()),
                            rename(c.body(), renaming),
                            c.unwrapAsserts(), renaming.at(c.pos())));
                }
                yield new Ast.Match(rename(m.scrutinee(), renaming), cases, m.origin(),
                        renaming.at(m.pos()), renaming.over(m.region()));
            }
            case Ast.If iff -> new Ast.If(rename(iff.cond(), renaming), rename(iff.then(), renaming),
                    rename(iff.els(), renaming), iff.origin(), renaming.at(iff.pos()),
                    renaming.over(iff.region()));
            // the success binder has its own BindingId, so a reference to it is not a candidate for
            // substitution, and neither the construction nor the else value can reach it
            case Ast.IfConstructed ic -> new Ast.IfConstructed(
                    rename(ic.construct(), renaming), renaming.copy().of(ic.binder()),
                    rename(ic.then(), renaming),
                    Ast.mapArms(ic.els(), body -> rename(body, renaming)),
                    ic.origin(), renaming.at(ic.pos()), renaming.over(ic.region()));
            case Ast.LetIn li -> {
                Ast.Expr value = rename(li.value(), renaming);
                Ast.Expr body = rename(li.body(), renaming);
                yield new Ast.LetIn(renaming.copy().of(li.binder()), value, li.declaredType(), li.annotated(),
                        li.opens(), body, renaming.at(li.pos()), renaming.over(li.region()));
            }
            // A body already expanded once, being copied into another caller. The signature comes
            // along as it stands: what its variables stand for is settled while each copy is typed,
            // from that copy's own arguments, so two copies decide separately without the variables
            // having to be minted again here.
            case Ast.Expansion ex -> {
                List<Ast.Bound> bound = new ArrayList<>();
                for (Ast.Bound b : ex.bound()) {
                    bound.add(new Ast.Bound(renaming.copy().of(b.binder()), b.declaredType(),
                            rename(b.value(), renaming)));
                }
                List<Ast.Given> given = new ArrayList<>();
                for (Ast.Given g : ex.given()) {
                    given.add(new Ast.Given(g.declaredType(),
                            rename(g.value(), renaming), g.applied(),
                            g.arrivesAs()));
                }
                yield new Ast.Expansion(ex.callee(), ex.application(), bound, given,
                        ex.declaredReturn(), rename(ex.body(), renaming),
                        renaming.at(ex.pos()), renaming.over(ex.region()));
            }
            case Ast.ListLit lit -> new Ast.ListLit(renameList(lit.elements(), renaming),
                    renaming.at(lit.pos()), renaming.over(lit.region()));
            case Ast.Tuple tup -> new Ast.Tuple(renameList(tup.elements(), renaming),
                    renaming.at(tup.pos()), renaming.over(tup.region()));
            case Ast.TupleGet tg -> new Ast.TupleGet(rename(tg.tuple(), renaming), tg.index(), tg.arity(),
                    renaming.at(tg.pos()), renaming.over(tg.region()));
            case Ast.ListComp comp -> new Ast.ListComp(rename(comp.element(), renaming),
                    renameList(comp.guards(), renaming), comp.origin(), renaming.at(comp.pos()),
                    renaming.over(comp.region()));
            case Ast.Block block -> {
                List<Ast.Binder> params = new ArrayList<>();
                for (Ast.Binder p : block.params()) {
                    params.add(renaming.copy().of(p));
                }
                yield new Ast.Block(params,
                        rename(block.body(), renaming),
                        renaming.at(block.pos()), renaming.over(block.region()));
            }
            case Ast.IntLit lit -> renaming.stamps()
                    ? new Ast.IntLit(lit.value(), renaming.at(lit.pos()), renaming.over(lit.region()))
                    : e;
            case Ast.DecimalLit lit -> renaming.stamps()
                    ? new Ast.DecimalLit(lit.value(), renaming.at(lit.pos()),
                            renaming.over(lit.region()))
                    : e;
            case Ast.StringLit lit -> renaming.stamps()
                    ? new Ast.StringLit(lit.value(), renaming.at(lit.pos()),
                            renaming.over(lit.region()))
                    : e;
            case Ast.BoolLit lit -> renaming.stamps()
                    ? new Ast.BoolLit(lit.value(), renaming.at(lit.pos()),
                            renaming.over(lit.region()))
                    : e;
            // it names nothing, so a substitution has nothing to rewrite in it
            case Ast.Unreachable u -> renaming.stamps()
                    ? new Ast.Unreachable(u.reason(), renaming.at(u.pos()), renaming.over(u.region()))
                    : e;
        };
    }

    /**
     * Whether expanding this helper leaves the positions in its body alone. A module-own helper does:
     * its body lies in the user's file, so it is already where a diagnostic should point. A lambda
     * given to a fn parameter does too: it is the caller's own code, and a lambda written in a prelude
     * body was stamped with the call site when that body was renamed, so either way its positions are
     * the ones to report. Everything else is a prelude helper, whose body lies in the shipped source of
     * {@code souther.*} and is stamped with the call site instead.
     */
    private boolean keepsItsPositions(Ast.Apply call) {
        return switch (call.denotes()) {
            // a lambda, wherever it came from: the caller wrote it, or a prelude body wrote it and
            // was stamped with the call site when that body was renamed
            case ValueName.Local _ -> true;
            case ValueName.Helper helper -> helper.module().equals(table.module());
            case ValueName.Stdlib _, ValueName.Behavior _, ValueName.OfType _,
                    ValueName.Builtin _ -> false;
        };
    }

    /**
     * One name renamed — what {@link #rename} does wherever a name stands, whether that is an
     * expression of its own or the name a spread holds.
     *
     * <p>A substituted name keeps what the argument resolved to, so a named function handed to a
     * combinator stays the helper it is rather than becoming a binding of that spelling.
     */
    /**
     * A name in the copy, reading whatever it reads here.
     *
     * <p>Three cases, and they differ in whether the characters this name stands at still spell it.
     * A parameter read becomes a read of the binding this expansion made, which is this pass's
     * however much it reads like the parameter — the same thing {@link Copy#of(Ast.Binder)} says
     * about the binder. A copy stamped with the call site is read against the caller's file, and the
     * occurrence it was written at is in the callee's. Neither is written where it stands, so
     * neither keeps an occurrence; both keep somewhere to complain and the stretch of source the
     * name they replaced was read over.
     *
     * <p>The third is an ordinary name in a body keeping its own positions, and it keeps its
     * occurrence with them. Rebuilding one from {@link Ast.Var#name()} and a position — which is
     * what this did — takes the canonical name and measures it at the anchor, so a decomposed
     * spelling comes out of an expansion a unit short and a qualified one written over a line break
     * comes out as far as its spelling is long.
     */
    private Ast.Var renameVar(Ast.Var v, Renaming renaming) {
        if (!(v instanceof Ast.Var.Denoting)) {
            return v;   // it names nothing, so there is nothing to rename it to
        }
        Substituted stands = renaming.substituted(v.denotes());
        if (stands != null) {
            return Ast.Var.respelled(stands.name(), stands.denotes(), stands.reachedAs(),
                    renaming.at(v.pos()), renaming.over(v.region()));
        }
        ValueName denotes = renaming.copy().of(v.denotes());
        if (renaming.stamps()) {
            return Ast.Var.respelled(v.name(), denotes, v.reachedAs(),
                    renaming.at(v.pos()), renaming.over(v.region()));
        }
        return new Ast.Var.Denoting(v.written(), denotes, v.reachedAs(), v.region());
    }

    private List<Ast.Expr> renameList(List<Ast.Expr> es, Renaming renaming) {
        List<Ast.Expr> out = new ArrayList<>();
        for (Ast.Expr e : es) {
            out.add(rename(e, renaming));
        }
        return out;
    }

    /**
     * The value a spread copies, or null where it copies something else — a parameter, a binding, or
     * a name that merely shares a value's spelling.
     *
     * <p>The spread carries what it resolved to, so this asks that rather than matching the spelling
     * against the module's definitions: a binding in force wins over a declaration, and a spread is
     * no exception.
     */
    private Ast.FnDef valueSpread(Ast.Var spread) {
        if (!(spread instanceof Ast.Var.Denoting)
                || !(spread.denotes() instanceof ValueName.Helper)) {
            return null;
        }
        // by the name it is reached by here, which for another module's value is the qualified one.
        // Asked of what the name reaches and not of what this module has as its own fns: a published
        // value is substituted where it is spread exactly as one declared here is, and it is not one
        // of this module's fns — nothing emits a value.
        String reached = spread.reaches();
        Ast.FnDef value = table.reached(reached);
        return value == null || !value.params().isEmpty() || value.body() == null
                || graph.recurses(reached) ? null : value;
    }

    /**
     * Whether anything in {@code e} reads {@code binding}.
     *
     * <p>It asks what each name denotes, so a binder inside {@code e} that spells its name the same
     * is another binding and answers no. Nothing here tracks scope, because the tree already carries
     * the answer scope decided: that is what resolution is for.
     */
    private static boolean references(Ast.Expr e, BindingId binding) {
        ValueName denotes = switch (e) {
            case Ast.Var.Denoting v -> v.denotes();
            case Ast.Apply c when c.function() instanceof Ast.Var.Denoting -> c.denotes();
            default -> null;
        };
        if (denotes instanceof ValueName.Local local && local.id().equals(binding)) {
            return true;
        }
        boolean[] found = {false};
        forEachChild(e, child -> found[0] |= references(child, binding));
        return found[0];
    }

    /**
     * Runs {@code collect} over everything {@code work} reaches, following the values it reads.
     *
     * <p>An expression alone stops at the reference. A value is substituted where it is named
     * (ADR-0072), so the body of a value a body reads stands in that body — what that body names is
     * named there, and a declaration reached only through a value is reached. The bodies are followed
     * as far as they name each other, which is how a chain of values holds.
     *
     * <p>What is collected is the caller's question and not this walk's: which helpers a row applies
     * is one question, which declarations a module reaches at all is another. {@code work} is drained,
     * and what is seeded into it is the caller's too.
     */
    static void followingValues(Deque<Ast.Expr> work, Map<String, Ast.FnDef> table,
                                java.util.function.Consumer<Ast.Expr> collect) {
        Set<String> read = new LinkedHashSet<>();
        while (!work.isEmpty()) {
            Ast.Expr e = work.poll();
            collect.accept(e);
            Set<String> named = new LinkedHashSet<>();
            ValueCycles.valuesRead(e, table, named);
            for (String value : named) {
                Ast.FnDef def = table.get(value);
                if (def != null && def.params().isEmpty()
                        && def.body() instanceof Ast.FnBody.Written w && read.add(value)) {
                    work.add(w.expr());
                }
            }
        }
    }

    /**
     * The declarations {@code e} names, applied or not.
     *
     * <p>Which declarations a module reaches, which is what decides the methods it has to emit. A
     * recursive helper written where a value goes — {@code apply1(spin, n)} — is reached as surely as
     * one that is called: the expansion eta-expands it, and what stands there afterwards is a call to
     * a method that has to be somewhere. Asked of what a name denotes, so a parameter spelled like a
     * helper is the parameter.
     */
    private static void helpersNamedIn(Ast.Expr e, Map<String, Ast.FnDef> table, Set<String> out) {
        switch (e) {
            // `List.fold` desugars to `List.foldFrom` before inlining, so a body that folds reaches
            // the recursive `foldFrom` and not the wrapper it wrote.
            case Ast.Apply call when call.function() instanceof Ast.Var.Denoting callee
                    && !(callee.denotes() instanceof ValueName.Local) -> {
                String fn = "List.fold".equals(call.reaches()) ? "List.foldFrom" : call.reaches();
                if (table.containsKey(fn)) {
                    out.add(fn);
                }
            }
            case Ast.Var.Denoting v when v.denotes() instanceof ValueName.Helper
                    || v.denotes() instanceof ValueName.Stdlib -> {
                if (table.containsKey(v.reaches())) {
                    out.add(v.reaches());
                }
            }
            default -> { }
        }
        forEachChild(e, c -> helpersNamedIn(c, table, out));
    }

    /**
     * The helpers of {@code table} that {@code e} calls, added to {@code out}.
     *
     * <p>Static because the value-cycle check asks it of a table it builds for itself, before an
     * inliner exists. One walk either way: an edge of this graph is what it is, and a reader that
     * counted a different set of them would be reading a different graph.
     */
    static void helperCallsIn(Ast.Expr e, Map<String, Ast.FnDef> table, Set<String> out) {
        // Applying a function-typed parameter, or a binding holding a function, is not a call to
        // whatever else bears that name. The call carries what it resolved to, so it is asked rather
        // than matched against the helper table — a parameter named like a helper was reaching the
        // graph as a call to that helper, which made `let f (g: (Int) -> Int) = g(1)` recursive.
        if (e instanceof Ast.Apply call && call.function() instanceof Ast.Var.Denoting callee
                && !(callee.denotes() instanceof ValueName.Local)) {
            // `List.fold` desugars to `List.foldFrom` before inlining, so a body that folds reaches the
            // recursive `foldFrom` — recursion classification and prelude-injection must see that.
            String fn = "List.fold".equals(call.reaches()) ? "List.foldFrom" : call.reaches();
            if (table.containsKey(fn)) {
                out.add(fn);
            }
        }
        forEachChild(e, c -> helperCallsIn(c, table, out));
    }

    /** Applies {@code f} to every direct subexpression of {@code e}; the one exhaustive walk
     * lives on the AST, so a node kind added later cannot be skipped here unnoticed. */
    private static void forEachChild(Ast.Expr e, java.util.function.Consumer<Ast.Expr> f) {
        Ast.forEachChild(e, f);
    }
}
