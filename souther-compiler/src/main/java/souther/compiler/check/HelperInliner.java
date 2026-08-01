package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
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
import java.util.Set;
import java.util.function.Predicate;

/**
 * Expands calls to helper {@code fn}s inline (spec 12.5: a named helper is the same as an inline block).
 *
 * <p>A helper fn is a {@code fn} with no matching behavior — it writes its own parameter types
 * (spec 13.1) and, unlike a behavior fn, is not lowered to a class of its own. Instead every call
 * {@code h(a, b)} is rewritten to {@code let $k_p1 = a in let $k_p2 = b in <body>}, with the
 * helper's parameters α-renamed to fresh {@code $}-prefixed names so they cannot capture a caller
 * local (a source identifier never starts with {@code $}). Because the body is spliced into the
 * caller, the caller's construction-permission check, {@code depends on} inference, and codegen all
 * see the helper's constructions and injected calls directly — exactly as if the code had been
 * written inline (spec 12.5). Helpers must not recurse (directly or indirectly), which keeps the
 * expansion finite; a cycle is rejected up front.
 */
public final class HelperInliner {

    private final Map<String, Ast.FnDef> helpers;   // prelude + module-own, keyed by name (inlining)
    private final Map<String, Ast.FnDef> own;       // the module's own helpers (standalone check)
    private final Set<String> recursive = new HashSet<>();   // own helpers on a call cycle (spec 13.1)
    private final Map<String, LambdaOrigin> lambdaOrigins = new HashMap<>();   // $k_p -> where it was written
    private int counter = 0;

    /** Where a lambda given to a function parameter was written: the parameter it fills, the helper
     * that declares that parameter, and the lambda's own position. The lambda is inlined under a
     * synthetic {@code $k_p} name, which must never reach a diagnostic — an error about it is
     * reported against these instead. */
    private record LambdaOrigin(String param, String owner, SourcePos pos) {}

    private HelperInliner(Map<String, Ast.FnDef> helpers, Map<String, Ast.FnDef> own) {
        this.helpers = helpers;
        this.own = own;
    }

    /** A helper is a fn whose name is not a behavior's; behavior fns are lowered on their own. The
     * auto-imported prelude helpers (spec §reserved-namespace) join the inlining map so a bare
     * {@code not(x)} expands at any call site; a module-own helper of the same name shadows one. */
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
        Map<String, Ast.FnDef> own = helpersOf(module);
        Map<String, Ast.FnDef> table = new LinkedHashMap<>(imported);
        table.putAll(own);
        HelperInliner inliner = new HelperInliner(withPrelude(table), new LinkedHashMap<>(own));
        inliner.classifyRecursion();
        inliner.rejectValueCycles();
        inliner.computeReferencedPreludeRecursive(module);
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
    public static HelperInliner forHelpers(Map<String, Ast.FnDef> own) {
        return forHelpers(own, InliningPolicy.FULL);
    }

    /**
     * The same, resolving only what {@code policy} says to resolve.
     *
     * <p>{@link InliningPolicy#DISCHARGE} leaves the standard library out of the table, so a call to
     * one of its operations is not a helper call here and survives as written. Nothing else changes:
     * a module's own helper is expanded, and a recursive call is left standing, by the same rules.
     */
    public static HelperInliner forHelpers(Map<String, Ast.FnDef> own, InliningPolicy policy) {
        return forHelpers(own, Map.of(), policy);
    }

    /**
     * The same, with the definitions other modules publish to this one joining the table.
     *
     * <p>They are in the table and not in {@code own}, as they are for {@link #forModule}: an imported
     * definition is one this module expands and not one it declares.
     */
    public static HelperInliner forHelpers(Map<String, Ast.FnDef> own,
                                           Map<String, Ast.FnDef> imported, InliningPolicy policy) {
        // In the order they are written, so a module with two helpers to complain about complains
        // about the earlier one first.
        Map<String, Ast.FnDef> joined = new LinkedHashMap<>(imported);
        joined.putAll(own);
        Map<String, Ast.FnDef> table = policy == InliningPolicy.FULL
                ? withPrelude(joined) : joined;
        HelperInliner inliner = new HelperInliner(table, new LinkedHashMap<>(own));
        inliner.classifyRecursion();
        inliner.rejectValueCycles();
        return inliner;
    }

    /** prelude helpers are keyed by their qualified name (`List.map`); a module's own helpers by their
     * bare name (`対象明細`), and a definition another module publishes by the qualified name it is
     * reached by here. A qualified call resolves to whichever of the two declared it, a bare call to
     * the module's own — the standard library has no bare names (spec §stdlib). */
    private static Map<String, Ast.FnDef> withPrelude(Map<String, Ast.FnDef> helpers) {
        Map<String, Ast.FnDef> table = new HashMap<>(Prelude.helpers());
        table.putAll(helpers);
        return table;
    }

    /** A module's helpers: the fns that implement no behavior, keyed by name. */
    public static Map<String, Ast.FnDef> helpersOf(Ast.Module module) {
        Set<String> behaviorNames = new HashSet<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            behaviorNames.add(b.name());
        }
        Map<String, Ast.FnDef> own = new LinkedHashMap<>();
        for (Ast.FnDef fn : module.fns()) {
            if (!behaviorNames.contains(fn.name())) {
                own.put(fn.name(), fn);
            }
        }
        return own;
    }

    /** Prelude recursive helpers this module reaches, by qualified name (`List.foldFrom`). A prelude
     * recursive helper is not inlined (it would expand forever); instead it is emitted as one of this
     * module's own methods, exactly like a module-own recursive helper (see {@link
     * #injectedRecursiveHelpers}). Only the ones actually reached are emitted. */
    private final Set<String> referencedPreludeRecursive = new java.util.LinkedHashSet<>();

    /** The helpers this module's example rows apply, which need a method for that reason alone. */
    private final Set<String> exampleHelpers = new java.util.LinkedHashSet<>();

    /** Walks the module's fn bodies and data invariants, collecting the prelude recursive helpers they
     * reach transitively — those must be emitted as this module's own methods. */
    private void computeReferencedPreludeRecursive(Ast.Module module) {
        Set<String> reachable = new HashSet<>();
        java.util.Deque<String> work = new java.util.ArrayDeque<>();
        for (Ast.FnDef fn : module.fns()) {
            collectHelperCalls(fn.body(), reachable);
        }
        for (Ast.Def d : module.defs()) {
            if (d instanceof Ast.Data data) {
                for (Ast.InvariantClause clause : data.invariants()) {
                    collectHelperCalls(clause.expr(), reachable);
                }
            }
        }
        forEachExampleExpr(module, e -> collectHelperCalls(e, reachable));
        work.addAll(reachable);
        while (!work.isEmpty()) {
            Set<String> calls = callsOf.get(work.poll());
            if (calls == null) {
                continue;
            }
            for (String c : calls) {
                if (reachable.add(c)) {
                    work.add(c);
                }
            }
        }
        for (String name : reachable) {
            if (recursive.contains(name) && !own.containsKey(name)) {
                referencedPreludeRecursive.add(name);
            }
        }
        exampleHelpers.addAll(exampleHelpers(module, helpers));
        exampleHelpers.removeAll(referencedPreludeRecursive);
        exampleHelpers.removeIf(recursive::contains);   // already emitted as a recursive helper
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
     * <p>A helper with no body to emit is not here: an intrinsic is implemented in Java, and one whose
     * body produces a function has no value to hand back. A row applying either is refused where it is
     * evaluated, by that reason.
     */
    public static Set<String> exampleHelpers(Ast.Module module, Map<String, Ast.FnDef> table) {
        Set<String> called = new LinkedHashSet<>();
        HelperInliner reader = new HelperInliner(table, table);
        // A row may name a value rather than write the input again (ADR-0072), and that value's body
        // is read the way the row's own text is — so a helper it applies is applied when the row is
        // evaluated. The bodies are followed as far as they name each other, which is how a chain of
        // values holds.
        Set<String> valuesRead = new LinkedHashSet<>();
        Deque<Ast.Expr> work = new ArrayDeque<>();
        forEachExampleExpr(module, work::add);
        while (!work.isEmpty()) {
            Ast.Expr e = work.poll();
            reader.collectHelperCalls(e, called);
            Set<String> named = new LinkedHashSet<>();
            reader.collectValueRefs(e, named);
            for (String value : named) {
                Ast.FnDef def = table.get(value);
                if (def != null && def.params().isEmpty() && def.body() != null
                        && valuesRead.add(value)) {
                    work.add(def.body());
                }
            }
        }
        Set<String> out = new LinkedHashSet<>();
        for (String name : called) {
            Ast.FnDef helper = table.get(name);
            if (helper != null && helper.body() != null && helper.intrinsicKey() == null
                    && !helper.params().isEmpty() && !Elaborator.producesFunction(helper.body())) {
                out.add(name);
            }
        }
        return out;
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
            if (own.containsKey(name)) {
                continue;
            }
            Ast.FnDef def = helpers.get(name);
            out.put(name, new Ast.FnDef(name, def.params(), def.declaredReturn(), def.intrinsicKey(),
                    def.body(), def.partial(), def.pos()));
        }
        return out;
    }

    /** The recursive helpers this module emits as methods: its own recursive helpers plus the prelude
     * recursive helpers it reaches (spec 13.1). A call to any of them is left standing by {@link
     * #inline}. The internal {@code recursive} set additionally holds prelude recursive helpers the
     * module does not reach, so {@code inline} never expands one that slips in through a nested body. */
    public Set<String> recursiveHelpers() {
        Set<String> result = new java.util.LinkedHashSet<>();
        for (String name : recursive) {
            if (own.containsKey(name)) {
                result.add(name);
            }
        }
        result.addAll(referencedPreludeRecursive);
        return result;
    }

    /** The prelude recursive helpers this module reaches, renamed to their qualified names so they are
     * emitted as the module's own methods — a prelude {@code let foldFrom} is reached as {@code
     * List.foldFrom}, and its self-call already reads {@code List.foldFrom}. */
    public Map<String, Ast.FnDef> injectedRecursiveHelpers() {
        Map<String, Ast.FnDef> out = new java.util.LinkedHashMap<>();
        for (String qualified : referencedPreludeRecursive) {
            Ast.FnDef def = helpers.get(qualified);
            out.put(qualified, new Ast.FnDef(qualified, def.params(), def.declaredReturn(),
                    def.intrinsicKey(), def.body(), def.partial(), def.pos()));
        }
        return out;
    }

    /** The module's own helper fns, keyed by name (for the standalone signature check). The
     * auto-imported prelude helpers are excluded — they are validated once, on their own. */
    public Map<String, Ast.FnDef> helpers() {
        return own;
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
        Ast.Expr closed = recursive.contains(fn.name()) ? inlineRecursiveBody(fn) : inline(fn.body());
        return new Ast.FnDef(qualified(module, fn.name()), fn.params(), fn.declaredReturn(), null,
                publishedBy(qualifyHelpersOf(closed, module), module), fn.partial(), fn.pos());
    }

    /**
     * {@code e} with every construction in it marked as {@code module}'s.
     *
     * <p>What a published body builds is built where that body was written, and the reader is handed
     * the result. Expanding it puts the construction in the reader's body, where the permission check
     * would ask the reader to declare it — for a type the declaring module may keep to itself, under a
     * name the reader has none of. The mark is what tells the two apart afterwards, and it names the
     * module rather than saying only that the construction came from somewhere: a body may build a
     * type of a third module, and that one is nobody's to hand over (ADR-0059).
     */
    private static Ast.Expr publishedBy(Ast.Expr e, String module) {
        Ast.Expr rebuilt = Ast.mapChildren(e, c -> publishedBy(c, module));
        return switch (rebuilt) {
            case Ast.NewData nd -> nd.publishedBy(module);
            // a unit data is constructed by being named, so the name is where it says where it came
            // from — there is no construction node to say it on
            case Ast.Var v when v.denotes() instanceof ValueName.OfType named ->
                    v.denoting(named.publishedBy(module));
            default -> rebuilt;
        };
    }

    /**
     * {@code e} with every construction in it marked as one a value made.
     *
     * <p>A value is substituted at each reference, so what its definition built ends up standing in
     * the body that named it, as the node that body's own construction would be. The mark is what
     * keeps the permission check reading the model rather than the substitution: a behavior stating a
     * rule against a named limit compares against a value, and originates none of it. A limit is
     * written as a value so that the figure has one place to live and one comment saying where it
     * comes from, and naming it is not supposed to cost every rule that reads it an authority it does
     * not use.
     *
     * <p>Unlike a published body's mark this names no module. What the value built is the value
     * definition's however the type got its declaration, and a behavior reading the name is not the
     * one that made it either way. A helper is the other case and stays the other case: its body is
     * checked as though it had been written inline, which is what tells a helper from a behavior.
     *
     * <p>Three things can stand for a construction and each takes the mark. A construction node
     * carries its own; a unit data is constructed by being named, so the name carries it; and a
     * recursive helper is lowered to a method rather than expanded, so what it builds stays behind a
     * call, and the call carries it. Without the third, whether a value's constructions belonged to
     * the value would turn on whether a helper on the way could be expanded — the substitution
     * showing through the rule again, in the one place expansion cannot reach.
     */
    private static Ast.Expr carriedByValue(Ast.Expr e) {
        Ast.Expr rebuilt = Ast.mapChildren(e, HelperInliner::carriedByValue);
        return switch (rebuilt) {
            case Ast.NewData nd -> nd.carriedByValue();
            case Ast.Var v when v.denotes() instanceof ValueName.OfType named ->
                    v.denoting(named.carriedByValue());
            case Ast.Call call -> call.carriedByValue();
            default -> rebuilt;
        };
    }

    /** How a definition of {@code module} is named outside it. */
    public static String qualified(String module, String name) {
        return module + "." + name;
    }

    /**
     * {@code m} with every name that denotes another module's definition written qualified.
     *
     * <p>A reader writes an imported value or helper bare, and the pair (module, name) is what it
     * denotes. From here on the two agree: the spelling a body carries is the definition's identity,
     * so everything downstream — the table a call is expanded against, the method a recursive helper
     * is emitted as — reads the identity by reading the name, and two modules publishing a
     * {@code tally} stay two definitions. Done once, here, because the spelling travels as far as the
     * emitted method name; deciding it at each reader is how one of them comes to disagree.
     */
    public static Ast.Module qualifyImports(Ast.Module m) {
        List<Ast.FnDef> fns = new ArrayList<>();
        for (Ast.FnDef fn : m.fns()) {
            fns.add(fn.body() == null ? fn
                    : new Ast.FnDef(fn.name(), fn.params(), fn.declaredReturn(), fn.intrinsicKey(),
                            qualifyForeign(fn.body(), m.name()), fn.partial(), fn.pos()));
        }
        List<Ast.Def> defs = qualifiedInvariants(m);
        List<Ast.Example> examples = new ArrayList<>();
        for (Ast.Example ex : m.examples()) {
            List<Ast.ExampleRow> rows = new ArrayList<>();
            for (Ast.ExampleRow row : ex.rows()) {
                List<Ast.Expr> inputs = new ArrayList<>();
                for (Ast.Expr in : row.inputs()) {
                    inputs.add(qualifyForeign(in, m.name()));
                }
                List<Ast.With> withs = new ArrayList<>();
                for (Ast.With w : row.withs()) {
                    withs.add(new Ast.With(w.dep(), qualifyForeign(w.value(), m.name()), w.pos()));
                }
                rows.add(new Ast.ExampleRow(row.description(), inputs, withs,
                        qualifyForeign(row.expected(), m.name()), row.pos()));
            }
            examples.add(new Ast.Example(ex.target(), rows, ex.pos()));
        }
        List<Ast.Fake> fakes = new ArrayList<>();
        for (Ast.Fake fake : m.fakes()) {
            List<Ast.FakeRow> rows = new ArrayList<>();
            for (Ast.FakeRow row : fake.rows()) {
                List<Ast.Expr> inputs = null;
                if (row.inputs() != null) {   // a default row matches anything and writes none
                    inputs = new ArrayList<>();
                    for (Ast.Expr in : row.inputs()) {
                        inputs.add(qualifyForeign(in, m.name()));
                    }
                }
                rows.add(new Ast.FakeRow(inputs, qualifyForeign(row.output(), m.name()),
                        row.isDefault(), row.pos()));
            }
            fakes.add(new Ast.Fake(fake.target(), rows, fake.pos()));
        }
        return new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(), defs,
                m.behaviors(), fns, examples, fakes, m.exampleFileTarget(), m.pos());
    }

    /** {@code m} with the foreign names in its invariants written qualified, and nothing else
     * changed. An invariant is read before the bodies are — settled here, classified for discharge
     * there — so this is the part of {@link #qualifyImports} that has to be available on its own. */
    public static Ast.Module withQualifiedInvariants(Ast.Module m) {
        List<Ast.Def> defs = qualifiedInvariants(m);
        return defs.equals(m.defs()) ? m
                : new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(), defs,
                        m.behaviors(), m.fns(), m.examples(), m.fakes(), m.exampleFileTarget(),
                        m.pos());
    }

    /** {@code m}'s declarations with every name in an invariant that denotes another module's
     * definition written qualified. */
    private static List<Ast.Def> qualifiedInvariants(Ast.Module m) {
        List<Ast.Def> defs = new ArrayList<>();
        for (Ast.Def def : m.defs()) {
            defs.add(def instanceof Ast.Data d && !d.invariants().isEmpty()
                    ? new Ast.Data(d.name(), d.newtype(), d.includes(), d.fields(),
                            Ast.mapClauses(d.invariants(), inv -> qualifyForeign(inv, m.name())),
                            d.decoder(), d.encoder(), d.pos())
                    : def);
        }
        return defs;
    }

    /** {@code e} with every name denoting a helper of a module other than {@code self} written
     * qualified. */
    private static Ast.Expr qualifyForeign(Ast.Expr e, String self) {
        return qualifyHelpers(e, helper -> !helper.module().equals(self));
    }

    /** {@code e} with every name still denoting a helper of {@code module} written qualified. Only a
     * recursive helper survives closing, so this is what those calls become. */
    private static Ast.Expr qualifyHelpersOf(Ast.Expr e, String module) {
        return qualifyHelpers(e, helper -> helper.module().equals(module));
    }

    /**
     * {@code e} with every name denoting a helper {@code which} accepts written qualified.
     *
     * <p>It reads what a name denotes rather than how it is spelled: a binding of the same spelling is
     * a binding, and a prelude helper belongs to the prelude and keeps the qualified name it already
     * has. The new spelling is read off the same answer, so running this twice says what running it
     * once said.
     */
    private static Ast.Expr qualifyHelpers(Ast.Expr e, Predicate<ValueName.Helper> which) {
        Ast.Expr rebuilt = Ast.mapChildren(e, c -> qualifyHelpers(c, which));
        return switch (rebuilt) {
            case Ast.Call call when foreign(call.denotes(), which) ->
                    new Ast.Call(qualifiedName(call.denotes()), call.denotes(), call.args(),
                            call.origin(),
                            call.pos());
            case Ast.Var v when foreign(v.denotes(), which) ->
                    new Ast.Var(qualifiedName(v.denotes()), v.denotes(), v.pos());
            // a spread names a value the way any other position does, and `mapChildren` does not
            // reach it — it holds a name rather than an expression
            case Ast.NewData nd -> {
                List<Ast.ValueRef> spreads = new ArrayList<>();
                boolean changed = false;
                for (Ast.ValueRef spread : nd.spreads()) {
                    boolean qualify = foreign(spread.denotes(), which);
                    changed |= qualify;
                    spreads.add(qualify
                            ? new Ast.ValueRef(qualifiedName(spread.denotes()), spread.denotes(),
                                    spread.pos())
                            : spread);
                }
                yield changed
                        ? new Ast.NewData(nd.typeName(), nd.inits(), spreads,
                                nd.origin(), nd.pos())
                        : nd;
            }
            default -> rebuilt;
        };
    }

    /** Whether {@code denotes} is a helper {@code which} accepts. */
    private static boolean foreign(ValueName denotes, Predicate<ValueName.Helper> which) {
        return denotes instanceof ValueName.Helper helper && which.test(helper);
    }

    /**
     * The helpers {@code e} still reaches — what a body closed by {@link #closeAcross} could not
     * expand away, which is the recursive ones.
     *
     * <p>Each is given as what it denotes rather than as a spelling, because the two questions a
     * caller then has differ: which module declares it decides how it is keyed, and a binding that
     * shares a helper's spelling is not one of these at all.
     */
    public static Set<ValueName.Helper> helpersReached(Ast.Expr e) {
        Set<ValueName.Helper> out = new LinkedHashSet<>();
        collectHelpersOf(e, out);
        return out;
    }

    private static void collectHelpersOf(Ast.Expr e, Set<ValueName.Helper> out) {
        if (e == null) {
            return;
        }
        ValueName denotes = switch (e) {
            case Ast.Call call -> call.denotes();
            case Ast.Var v -> v.denotes();
            default -> null;
        };
        if (denotes instanceof ValueName.Helper helper) {
            out.add(helper);
        }
        if (e instanceof Ast.NewData nd) {
            for (Ast.ValueRef spread : nd.spreads()) {
                if (spread.denotes() instanceof ValueName.Helper helper) {
                    out.add(helper);
                }
            }
        }
        Ast.forEachChild(e, c -> collectHelpersOf(c, out));
    }

    /** The name a helper is reached by outside the module that declares it. Read off what the name
     * denotes, so applying it to a name already written this way answers the same thing. */
    private static String qualifiedName(ValueName denotes) {
        ValueName.Helper helper = (ValueName.Helper) denotes;
        return qualified(helper.module(), helper.name());
    }

    /**
     * Settles the helper parameter types the author left unwritten, then inlines the helper calls in
     * every data's {@code invariant}.
     *
     * <p>The two go together: expanding a call carries the parameter's type onto the binding the call
     * becomes, so a type settled afterwards would never reach this expansion (issue #178). An
     * invariant is inlined well before the module is lowered — an importer reads an included data's
     * invariant through the symbol table, so it must already be expanded there — which is why the
     * settling is done here as well as in {@link Lower}. It is idempotent: a parameter already typed
     * is left alone, and {@code Lower} settles what only the fully desugared module can determine.
     *
     * <p>An invariant is pure and cannot call an injected behavior (spec §invariant-expressions), so
     * nothing here needs the injected signatures to settle the helpers an invariant reaches.
     *
     * <p>{@code published} is what the modules this one imports offer it. An invariant names what is
     * in scope where it is written, and an imported definition is in scope there as it is in a body; it
     * is substituted here for the reason a body's is, so what the invariant carries afterwards names
     * nothing of the module that declared it. The names are written qualified first, because that is
     * the spelling the table is keyed by — {@link #qualifyImports} does it again for the bodies below,
     * and says the same thing both times.
     */
    public static Ast.Module withSettledInvariants(Ast.Module m, Symbols symbols,
                                                   Map<String, Ast.FnDef> published) {
        Ast.Module settled = withQualifiedInvariants(HelperParams.settle(m, symbols, Map.of()));
        return forModule(settled, published).withInlinedInvariants(settled);
    }

    /**
     * Inlines helper calls inside every data's {@code invariant}, so a rule named with a {@code let}
     * (e.g. {@code invariant 正の数(value)}) expands to its body before the invariant is type-checked
     * or emitted — the same lowering a behavior body gets (spec 12.5, §invariant-expressions).
     */
    /**
     * Each declaration's invariant in the representation the invariant-discharge analysis reads: the
     * helpers it can name expanded, the language's own operations left standing
     * ({@link InliningPolicy#DISCHARGE}). Keyed by the declaration's name in {@code m}.
     *
     * <p>This is the same settling {@link #withSettledInvariants} does, stopped one step earlier, and
     * it reads the same table: what the clause names is substituted whether this module declared it or
     * imported it. The settled form is what travels to an importer and what the backend emits; an
     * importer therefore reads an imported invariant in the settled form and finds nothing here for
     * it, which is where an imported clause falls outside the statically dischargeable fragment (spec
     * §invariant-discharge).
     */
    public static Map<TypeName, List<Ast.InvariantClause>> invariantsForDischarge(
            Ast.Module m, Symbols symbols, Map<String, Ast.FnDef> published) {
        Ast.Module settled = withQualifiedInvariants(HelperParams.settle(m, symbols, Map.of()));
        HelperInliner inliner =
                forHelpers(helpersOf(settled), published, InliningPolicy.DISCHARGE);
        Map<TypeName, List<Ast.InvariantClause>> out = new LinkedHashMap<>();
        for (Ast.Def def : settled.defs()) {
            if (def instanceof Ast.Data d && !d.invariants().isEmpty()) {
                out.put(new TypeName(m.name(), d.name()),
                        Ast.mapClauses(d.invariants(), inliner::inline));
            }
        }
        return out;
    }

    Ast.Module withInlinedInvariants(Ast.Module m) {
        List<Ast.Def> defs = new ArrayList<>();
        for (Ast.Def def : m.defs()) {
            if (def instanceof Ast.Data d && !d.invariants().isEmpty()) {
                defs.add(new Ast.Data(d.name(), d.newtype(), d.includes(), d.fields(),
                        Ast.mapClauses(d.invariants(), this::inline),
                        d.decoder(), d.encoder(), d.pos()));
            } else {
                defs.add(def);
            }
        }
        return new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(),
                defs, m.behaviors(), m.fns(), m.examples(), m.fakes(), m.exampleFileTarget(), m.pos());
    }

    /** The conjuncts of an invariant expression, flattened, in the order they are written — what a
     * reader sees as separate clauses. */
    public static List<Ast.Expr> conjunctsOf(Ast.Expr e) {
        if (e instanceof Ast.Binary b && b.op() == Ast.BinOp.AND) {
            List<Ast.Expr> out = new ArrayList<>(conjunctsOf(b.left()));
            out.addAll(conjunctsOf(b.right()));
            return out;
        }
        return List.of(e);
    }

    /** Looks up a helper by name across the prelude and the module's own helpers, or null if the
     * name is not a helper (a builtin, injected behavior, or unknown). Used to type-check a function
     * passed to a helper's function parameter against the declared type, at the call site. */
    public Ast.FnDef helper(String name) {
        return helpers.get(name);
    }

    /** {@code fold} is the one privileged loop primitive that takes a block (spec 18.4); its block is
     * the first argument and has two parameters (`(acc, x)`, spec §pipe). A bare name passed in its
     * place is sugar for a block that wraps a call. The map is from the combinator name to the block's
     * argument index. The other combinators (map/filter/all/any) are ordinary prelude helpers derived
     * from fold (ADR-0028), so they need no such desugaring — a name reaches their function parameter
     * directly. */
    private static final Map<String, Integer> BLOCK_ARG = Map.of("List.foldFrom", 0);

    /** {@code List.fold(step, seed, xs)} is sugar for {@code List.foldFrom(step, seed, xs, 0)} — the
     * walk from the head. Rewriting it here, before inlining, means the step reaches {@code foldFrom}
     * (the one recursive helper) directly rather than through a wrapper that would pass the function on
     * as a value. */
    private static Ast.Call desugarFold(Ast.Call call) {
        if (!call.fn().equals("List.fold") || call.args().size() != 3) {
            return call;
        }
        List<Ast.Expr> args = new ArrayList<>(call.args());
        args.add(new Ast.IntLit(0, call.pos()));
        return new Ast.Call("List.foldFrom", new ValueName.Stdlib("List.foldFrom"), args,
                ConstructionOrigin.own(),
                call.pos());
    }

    /** Inlines a recursive helper's own body, expanding the non-recursive helper calls it makes while
     * leaving its own parameters alone. A parameter that shares a module helper's name — {@code
     * foldFrom}'s function parameter {@code step} in a module that also defines a helper {@code step} —
     * is a parameter application, not a call to that helper, so the same-named helpers are hidden while
     * the body is expanded. */
    public Ast.Expr inlineRecursiveBody(Ast.FnDef h) {
        Map<String, Ast.FnDef> shadowed = new HashMap<>();
        for (Ast.FnParam p : h.params()) {
            Ast.FnDef hidden = helpers.remove(p.name());
            if (hidden != null) {
                shadowed.put(p.name(), hidden);
            }
        }
        try {
            return inline(h.body());
        } finally {
            helpers.putAll(shadowed);
        }
    }

    /** Keeps a helper's declared return type on the body spliced into the caller, as the annotation of
     * a binding the body flows through ({@code let $r0: Map<String, Int> = <body> in $r0}). A declared
     * return is a declaration into the body (spec §fn-declaration), and inlining is where it would
     * otherwise be lost: at a call site that expects nothing concrete — a generic parameter such as
     * {@code Map.toList}'s — the declaration is the only thing that can fix an empty-collection seed
     * inside the body.
     *
     * <p>Only a collection-bearing return type is carried. A scalar return has nothing to fix, and
     * leaving those bodies bare keeps a constant-foldable expression ({@code 金額(税込(100))}) a plain
     * expression for the compile-time invariant check. A union return is left alone too: the binding
     * would name one type where the body may produce several. */
    private Ast.Expr keepDeclaredReturn(Ast.FnDef helper, Ast.Expr body, SourcePos pos, int k) {
        Ast.RetType declared = helper.declaredReturn();
        if (declared == null || declared.cases().size() != 1
                || !carriesCollection(declared.cases().get(0))
                || mentionsTypeVar(declared.cases().get(0))) {
            return body;
        }
        String bound = "$r" + k;
        return Ast.LetIn.annotated(bound, body, declared, Ast.Var.local(bound, pos), pos);
    }

    /** Whether a written type has a collection anywhere inside it — the types whose element/value type
     * an empty literal leaves open until something declares it. */
    private static boolean carriesCollection(Ast.TypeTerm term) {
        if (!(term instanceof Ast.TypeRef ref)) {
            return false;   // a function type carries no collection a literal could leave open
        }
        if ("List".equals(ref.name()) || "Map".equals(ref.name()) || "Set".equals(ref.name())) {
            return true;
        }
        if (carriesCollection(ref.arg())) {
            return true;
        }
        if (ref.tupleElems() != null) {
            for (Ast.TypeTerm e : ref.tupleElems()) {
                if (carriesCollection(e)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Whether a written type has a type variable inside it. A generic declared return ({@code
     * Map.upsert}'s {@code Map<'k, 'a>}) says nothing concrete at a call site, so it is not carried —
     * the caller's own arguments are what fix those variables. */
    private static boolean mentionsRetTypeVar(Ast.RetType ret) {
        return ret != null && ret.cases().stream().anyMatch(HelperInliner::mentionsTypeVar);
    }

    private static boolean mentionsTypeVar(Ast.TypeTerm term) {
        if (term instanceof Ast.FnType fn) {
            return fn.params().stream().anyMatch(HelperInliner::mentionsRetTypeVar)
                    || mentionsRetTypeVar(fn.result());
        }
        if (!(term instanceof Ast.TypeRef ref)) {
            return false;
        }
        if (ref.name() != null && ref.name().startsWith("'")) {
            return true;
        }
        if (mentionsTypeVar(ref.arg())) {
            return true;
        }
        if (ref.tupleElems() != null) {
            for (Ast.TypeTerm e : ref.tupleElems()) {
                if (mentionsTypeVar(e)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * The parameters a call's callee declares, as the caller wrote the name: a helper's own, or —
     * for the {@code List.fold} sugar — {@code foldFrom}'s without the index the sugar supplies.
     * Null when the name is not a helper (a builtin, an injected behavior, or unknown).
     */
    private List<Ast.FnParam> declaredParams(Ast.Call call) {
        if (call.fn().equals("List.fold") && call.args().size() == 3) {
            Ast.FnDef foldFrom = helpers.get("List.foldFrom");
            return foldFrom == null ? null : foldFrom.params().subList(0, 3);
        }
        Ast.FnDef helper = helpers.get(call.fn());
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
    private void checkFunctionArgumentPlacement(Ast.Call call) {
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
                throw CompileException.of(
                        Diagnostic.of(null, "check.fn.argnotfn").title("check.fn.title")
                                .at(lambda.pos()).args(call.fn(), i + 1, param).build(),
                        "argument " + (i + 1) + " of `" + call.fn() + "` is `" + param
                                + "`, which does not take a function");
            }
            String shape = params.stream().map(Ast.FnParam::name)
                    .collect(java.util.stream.Collectors.joining(", "));
            throw CompileException.of(
                    Diagnostic.of(null, "check.fn.argorder").title("check.fn.title")
                            .at(lambda.pos())
                            .args(call.fn(), i + 1, param, fnParam + 1, params.get(fnParam).name(), shape)
                            .hint("check.fn.argorder.hint").build(),
                    "argument " + (i + 1) + " of `" + call.fn() + "` is `" + param
                            + "`, which does not take a function: the function goes to argument "
                            + (fnParam + 1) + " (`" + params.get(fnParam).name() + "`). Write `"
                            + call.fn() + "(" + shape + ")`.");
        }
    }

    /**
     * The helper a call applies, or null where it applies something else.
     *
     * <p>A call that resolved to a binding applies that binding, whatever else bears the name: a
     * helper's function-typed parameter is a binding, and expanding it as the helper it is spelled
     * like reported the wrong arity. The one binding that is expanded here is a lambda this pass
     * registered for a function parameter, under a {@code $}-name a source identifier cannot have —
     * it is bound to the lambda the caller wrote, so applying it is applying that lambda.
     */
    private Ast.FnDef appliedHelper(Ast.Call call) {
        if (call.denotes() instanceof ValueName.Local
                && !call.fn().startsWith("$") && !scopedLambdaNames.contains(call.fn())) {
            return null;
        }
        return helpers.get(call.fn());
    }

    /** Bindings this pass registered as helpers while their body is expanded: a lambda bound by a
     * block's {@code let}, which is applied where it is bound and so β-reduces like a named helper.
     * A {@code $}-name from a function argument is one too, and is told apart by its prefix. */
    private final Set<String> scopedLambdaNames = new HashSet<>();

    /** Rewrites every helper call in {@code e} to its inlined body. */
    public Ast.Expr inline(Ast.Expr e) {
        return switch (e) {
            case Ast.Call rawCall -> {
                checkFunctionArgumentPlacement(rawCall);
                Ast.Call call = desugarNamedBlock(desugarFold(rawCall));
                List<Ast.Expr> args = new ArrayList<>();
                for (Ast.Expr a : call.args()) {
                    args.add(inline(a));
                }
                Ast.FnDef helper = appliedHelper(call);
                if (helper == null || recursive.contains(call.fn())) {
                    // builtin, injected behavior, a function-typed parameter, or a recursive helper —
                    // a recursive helper is lowered to a method, so its call stays a Call (spec 13.1);
                    // only its args inline.
                    yield new Ast.Call(call.fn(), call.denotes(), args, call.origin(), call.pos());
                }
                if (args.size() != helper.params().size()) {
                    LambdaOrigin origin = lambdaOrigins.get(helper.name());
                    if (origin != null) {
                        // the callee is a lambda the caller wrote, applied by the combinator it was
                        // given to: report the parameter count against the lambda, not the synthetic
                        // name it is inlined under.
                        throw CompileException.of(
                                Diagnostic.of(null, "check.fn.blockparam.arity").title("check.fn.title")
                                        .at(origin.pos())
                                        .args(origin.param(), origin.owner(), args.size(),
                                                helper.params().size()).build(),
                                "the block passed to `" + origin.param() + "` of `let " + origin.owner()
                                        + "` takes " + args.size() + " argument(s) but is written with "
                                        + helper.params().size());
                    }
                    throw CompileException.of(
                            Diagnostic.of(null, "check.helper.arity").title("check.arity.title")
                                    .at(call.pos(), call.fn().length())
                                    .args(helper.name(), helper.params().size(), args.size()).build(),
                            "helper `let " + helper.name() + "` takes " + helper.params().size()
                                    + " argument(s) but is called with " + args.size());
                }
                int k = counter++;
                Map<String, String> subst = new HashMap<>();
                // what each substituted callee resolved to at the call site, so the expansion carries
                // the argument's own answer rather than deciding one for it
                Map<String, ValueName> substDenotes = new HashMap<>();
                Set<String> fnParams = new HashSet<>();
                Map<String, Ast.FnDef> scopedLambdas = new HashMap<>();   // lambdas given to fn params
                List<String> letNames = new ArrayList<>();
                List<Ast.Expr> letValues = new ArrayList<>();
                List<Ast.RetType> letTypes = new ArrayList<>();
                for (int i = 0; i < helper.params().size(); i++) {
                    Ast.FnParam p = helper.params().get(i);
                    Ast.Expr arg = args.get(i);
                    if (p.type() != null && p.type().asFn() != null) {
                        // a function argument is not a value, so it cannot be bound to a let. A named
                        // function is substituted directly (f(x) becomes inc(x)); a lambda is
                        // registered under a fresh name as a scoped helper, so each application of the
                        // parameter β-reduces to the lambda's body, as a let-bound lambda does (spec 12.5).
                        if (arg instanceof Ast.Var fnName) {
                            subst.put(p.name(), fnName.name());
                            substDenotes.put(p.name(), fnName.denotes());
                            fnParams.add(p.name());
                        } else if (arg instanceof Ast.Block lambda) {
                            String f = "$" + k + "_" + p.name();
                            subst.put(p.name(), f);
                            substDenotes.put(p.name(), new ValueName.Local(f, lambda.pos()));
                            fnParams.add(p.name());
                            List<Ast.FnParam> lparams = new ArrayList<>();
                            for (String lp : lambda.params()) {
                                lparams.add(new Ast.FnParam(lp, null, lambda.pos()));
                            }
                            // the lambda's body is caller code, so it is not renamed by this helper's
                            // substitution — only the enclosing helper body is.
                            scopedLambdas.put(f, new Ast.FnDef(f, lparams, null, null, lambda.body(), lambda.pos()));
                            lambdaOrigins.put(f, new LambdaOrigin(p.name(), helper.name(), lambda.pos()));
                        } else {
                            // Neither a name nor a lambda: a value written where the function goes —
                            // the argument-order mistake made with a named helper rather than a
                            // lambda. Named against the call as written, with the declared order.
                            List<Ast.FnParam> written = declaredParams(rawCall);
                            String shape = written == null ? null : written.stream()
                                    .map(Ast.FnParam::name)
                                    .collect(java.util.stream.Collectors.joining(", "));
                            Diagnostic.Builder d = Diagnostic.of(null, "check.fn.argnotvalue")
                                    .title("check.fn.title").at(arg.pos())
                                    .args(rawCall.fn(), i + 1, p.name(), shape);
                            if (shape != null) {
                                d.hint("check.fn.argnotvalue.hint");
                            }
                            throw CompileException.of(d.build(),
                                    "argument " + (i + 1) + " of `" + rawCall.fn() + "` is `" + p.name()
                                            + "`, which takes a function: pass a named function or a lambda"
                                            + (shape == null ? ""
                                                    : ". Write `" + rawCall.fn() + "(" + shape + ")`."));
                        }
                    } else {
                        String f = "$" + k + "_" + p.name();
                        subst.put(p.name(), f);
                        letNames.add(f);
                        letValues.add(arg);
                        // carry the parameter's declared type onto the binding, so a value known to
                        // be a sum (an annotated `s: S`) is not narrowed to the argument's specific
                        // case when the body is re-checked inline — a `match s` inside still sees S.
                        letTypes.add(p.type());
                    }
                }
                scopedLambdas.forEach(helpers::put);
                // a prelude helper's body is stamped with the call site, so errors inside it point at
                // the user's call, not at the shipped source of souther.* (a module-own helper keeps
                // its own positions, which already lie in the user's file).
                SourcePos at = own.containsKey(helper.name()) ? null : call.pos();
                Ast.Expr body = inline(rename(helper.body(), subst, substDenotes, fnParams, at));   // expand nested helpers too
                scopedLambdas.keySet().forEach(helpers::remove);
                body = keepDeclaredReturn(helper, body, call.pos(), k);
                // wrap innermost-first so the value parameters bind in declared order
                for (int i = letNames.size() - 1; i >= 0; i--) {
                    body = new Ast.LetIn(letNames.get(i), letValues.get(i), letTypes.get(i), body, call.pos());
                }
                yield body;
            }
            case Ast.FieldAccess fa -> new Ast.FieldAccess(inline(fa.target()), fa.field(), fa.pos());
            case Ast.Binary bin -> new Ast.Binary(bin.op(), inline(bin.left()), inline(bin.right()), bin.pos());
            case Ast.Neg neg -> new Ast.Neg(inline(neg.operand()), neg.pos());
            case Ast.NewData nd -> newData(nd);
            case Ast.Match m -> {
                List<Ast.Case> cases = new ArrayList<>();
                for (Ast.Case c : m.cases()) {
                    cases.add(new Ast.Case(c.caseTypes(), c.binding(), inline(c.body()), c.unwrapAsserts(), c.pos()));
                }
                yield new Ast.Match(inline(m.scrutinee()), cases, m.pos());
            }
            case Ast.If iff -> new Ast.If(inline(iff.cond()), inline(iff.then()), inline(iff.els()), iff.pos());
            case Ast.IfConstructed ic -> new Ast.IfConstructed(inline(ic.construct()), ic.binder(),
                    inline(ic.then()), Ast.mapArms(ic.els(), this::inline), ic.pos());
            case Ast.LetIn li when li.value() instanceof Ast.Block lambda -> {
                // a lambda bound to a local: register it as a scoped helper so each application in
                // the body expands inline (β-reduction), exactly like a named helper. Its parameters
                // are untyped, so their types flow in from the arguments at expansion. No runtime
                // closure is built as long as the lambda does not escape.
                if (mentions(lambda.body(), li.name())) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.fn.recursivelambda").title("check.fn.title")
                                    .at(lambda.pos()).args(li.name()).build(),
                            "the lambda bound to `" + li.name() + "` refers to itself; a recursive lambda"
                                    + " would not bottom out when expanded inline");
                }
                List<Ast.FnParam> params = new ArrayList<>();
                for (String p : lambda.params()) {
                    params.add(new Ast.FnParam(p, null, lambda.pos()));
                }
                Ast.FnDef synth = new Ast.FnDef(li.name(), params, null, null, lambda.body(), li.pos());
                Ast.FnDef shadowed = helpers.put(li.name(), synth);
                boolean fresh = scopedLambdaNames.add(li.name());
                Ast.Expr body = inline(li.body());
                if (fresh) {
                    scopedLambdaNames.remove(li.name());
                }
                if (shadowed == null) {
                    helpers.remove(li.name());
                } else {
                    helpers.put(li.name(), shadowed);
                }
                // if the name still occurs, the lambda was used as a value, not just applied — it
                // escapes, which needs a runtime closure. Keep the binding so the "a block is not a
                // value" check reports it.
                yield mentions(body, li.name())
                        ? new Ast.LetIn(li.name(), inline(lambda), li.declaredType(), li.annotated(), li.opens(), body, li.pos())
                        : body;
            }
            case Ast.LetIn li -> new Ast.LetIn(li.name(), inline(li.value()), li.declaredType(), li.annotated(), li.opens(),
                    inline(li.body()), li.pos());
            case Ast.ListLit lit -> new Ast.ListLit(inlineList(lit.elements()), lit.pos());
            case Ast.Tuple tup -> new Ast.Tuple(inlineList(tup.elements()), tup.pos());
            case Ast.TupleGet tg -> new Ast.TupleGet(inline(tg.tuple()), tg.index(), tg.arity(), tg.pos());
            case Ast.ListComp comp -> new Ast.ListComp(inline(comp.element()), inlineList(comp.guards()), comp.pos());
            case Ast.Block block -> new Ast.Block(block.params(), inline(block.body()), block.pos());
            case Ast.IntLit _ -> e;
            case Ast.DecimalLit _ -> e;
            case Ast.StringLit _ -> e;
            case Ast.BoolLit _ -> e;
            case Ast.Unreachable _ -> e;
            case Ast.Var v -> valueOf(v);
        };
    }

    /**
     * A name that denotes a value — a {@code let} written with no parameter list — expanded to the
     * expression it was defined as. A value is not module state: its body is elaborated where it was
     * declared and substituted at each reference, so nothing is held between them and there is no
     * order in which the module's values come into being.
     *
     * <p>A recursive value is left alone here; the recursion check reports it under its own name.
     * Anything else — a helper handed to a combinator by name, a binding, a unit data — is the name
     * itself.
     */
    private Ast.Expr valueOf(Ast.Var v) {
        if (!(v.denotes() instanceof ValueName.Helper)) {
            return v;
        }
        Ast.FnDef value = helpers.get(v.name());
        if (value == null || value.body() == null) {
            return v;
        }
        if (!value.params().isEmpty()) {
            // A helper named where a value goes is the function it names, written out: a lambda that
            // takes what the helper takes and applies it. The same value the author would get by
            // spelling the lambda, so nothing downstream has to know which of the two was written.
            // A recursive helper eta-expands too — the call inside stays the call it has to be.
            int k = counter++;
            List<String> params = new ArrayList<>();
            List<Ast.Expr> args = new ArrayList<>();
            for (int i = 0; i < value.params().size(); i++) {
                String p = "$v" + k + "_" + i;
                params.add(p);
                args.add(Ast.Var.local(p, v.pos()));
            }
            return inline(new Ast.Block(params,
                    new Ast.Call(v.name(), v.denotes(), args, ConstructionOrigin.own(), v.pos()), v.pos()));
        }
        if (recursive.contains(v.name())) {
            return v;
        }
        return carriedByValue(inline(value.body()));
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
        List<String> bound = new ArrayList<>();
        List<Ast.Expr> values = new ArrayList<>();
        List<Ast.ValueRef> spreads = new ArrayList<>();
        for (Ast.ValueRef spread : nd.spreads()) {
            Ast.FnDef value = valueSpread(spread);
            if (value == null) {
                spreads.add(spread);
                continue;
            }
            String name = "$s" + counter++ + "_" + spread.bare();
            bound.add(name);
            values.add(carriedByValue(inline(value.body())));
            spreads.add(Ast.ValueRef.local(name, spread.pos()));
        }
        Ast.Expr built = new Ast.NewData(nd.typeName(), inlineInits(nd.inits()), spreads,
                nd.origin(), nd.pos());
        for (int i = bound.size() - 1; i >= 0; i--) {
            built = new Ast.LetIn(bound.get(i), values.get(i), null, false, null, built, nd.pos());
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
            out.add(new Ast.FieldInit(i.name(), inline(i.value()), i.pos()));
        }
        return out;
    }

    /**
     * A helper fn passed to {@code fold} by name is sugar for a block that wraps a call:
     * {@code List.fold(step, seed, xs)} with a named {@code step} becomes
     * {@code List.fold(($b0, $b1) -> step($b0, $b1), seed, xs)} (spec 12.5, "名前で直接渡す。同じこと").
     * The generated block has one parameter per helper parameter, so a later arity check against
     * {@code fold} (it wants two) still applies. The block is then expanded inline like any other
     * helper call. Only {@code fold} needs this — map/filter/all/any are helpers whose function
     * parameter the inliner binds directly (see {@link #inline}).
     */
    private Ast.Call desugarNamedBlock(Ast.Call call) {
        Integer idx = BLOCK_ARG.get(call.fn());
        if (idx == null || idx >= call.args().size()
                || !(call.args().get(idx) instanceof Ast.Var v)) {
            return call;
        }
        Ast.FnDef helper = helpers.get(v.name());
        if (helper == null) {
            return call;   // a bare name that is not a helper is left for the type checker to report
        }
        int k = counter++;
        List<String> params = new ArrayList<>();
        List<Ast.Expr> callArgs = new ArrayList<>();
        for (int i = 0; i < helper.params().size(); i++) {
            String p = "$b" + k + "_" + i;
            params.add(p);
            callArgs.add(Ast.Var.local(p, v.pos()));
        }
        Ast.Block block = new Ast.Block(params,
                new Ast.Call(v.name(), v.denotes(), callArgs, ConstructionOrigin.own(), v.pos()), v.pos());
        List<Ast.Expr> args = new ArrayList<>(call.args());
        args.set(idx, block);
        return new Ast.Call(call.fn(), call.denotes(), args, call.origin(), call.pos());
    }

    /**
     * Capture-avoiding renaming of the helper's free parameter references. A binder that shadows a
     * parameter name (a {@code let}, {@code match} binding, or block parameter of the same name)
     * drops that name from the substitution for its scope, so an inner rebinding is left untouched.
     *
     * <p>{@code fnParams} names the parameters bound to a function argument: those are also rewritten
     * in call position, so an application {@code f(x)} of a function parameter becomes a call to the
     * fn it was passed. A value parameter is never rewritten as a callee, so a parameter that happens
     * to share a builtin's name still calls the builtin.
     *
     * <p>{@code at}, when non-null, is stamped onto every rebuilt node in place of its own position.
     * A prelude helper is expanded with the call site as {@code at}, so a type error inside its body
     * points at the user's call — {@code filter(xs, x -> x * 2)} — not at a line of {@code souther.list}
     * the user never wrote. A module-own helper passes {@code null} and keeps its own positions. The
     * caller's argument expressions, spliced in separately, keep their own positions either way.
     */
    private Ast.Expr rename(Ast.Expr e, Map<String, String> subst,
                            Map<String, ValueName> substDenotes, Set<String> fnParams,
                            SourcePos at) {
        return switch (e) {
            // a substituted name keeps what the argument resolved to, so a named function handed to a
            // combinator stays the helper it is rather than becoming a binding of that spelling
            case Ast.Var v -> subst.containsKey(v.name())
                    ? new Ast.Var(subst.get(v.name()),
                            substDenotes.getOrDefault(v.name(),
                                    new ValueName.Local(subst.get(v.name()), at(at, v.pos()))),
                            at(at, v.pos()))
                    : e;
            case Ast.FieldAccess fa -> new Ast.FieldAccess(rename(fa.target(), subst, substDenotes, fnParams, at), fa.field(), at(at, fa.pos()));
            case Ast.Call call -> {
                boolean renamed = fnParams.contains(call.fn()) && subst.containsKey(call.fn());
                String callee = renamed ? subst.get(call.fn()) : call.fn();
                // a renamed callee is the function argument this parameter was bound to, under the
                // name this expansion gave it; anything else keeps what the call already denoted
                // the argument's own answer where this expansion substituted one; a scoped lambda
                // was registered as a local just above, and a named function stays what it is
                ValueName denotes = renamed
                        ? substDenotes.getOrDefault(call.fn(), new ValueName.Local(callee, at(at, call.pos())))
                        : call.denotes();
                yield new Ast.Call(callee, denotes, renameList(call.args(), subst, substDenotes, fnParams, at),
                        call.origin(),
                        at(at, call.pos()));
            }
            case Ast.Binary bin -> new Ast.Binary(bin.op(), rename(bin.left(), subst, substDenotes, fnParams, at), rename(bin.right(), subst, substDenotes, fnParams, at), at(at, bin.pos()));
            case Ast.Neg neg -> new Ast.Neg(rename(neg.operand(), subst, substDenotes, fnParams, at), at(at, neg.pos()));
            case Ast.NewData nd -> {
                List<Ast.FieldInit> inits = new ArrayList<>();
                for (Ast.FieldInit i : nd.inits()) {
                    inits.add(new Ast.FieldInit(i.name(), rename(i.value(), subst, substDenotes, fnParams, at), at(at, i.pos())));
                }
                List<Ast.ValueRef> spreads = new ArrayList<>();
                for (Ast.ValueRef s : nd.spreads()) {
                    // `..param` copies the renamed binding, and stays the binding it now names
                    String renamed = subst.get(s.bare());
                    spreads.add(renamed == null ? s : Ast.ValueRef.local(renamed, at(at, s.pos())));
                }
                yield new Ast.NewData(nd.typeName(), inits, spreads, nd.origin(), at(at, nd.pos()));
            }
            case Ast.Match m -> {
                List<Ast.Case> cases = new ArrayList<>();
                for (Ast.Case c : m.cases()) {
                    Map<String, String> inner = c.binding() == null ? subst : without(subst, c.binding());
                    cases.add(new Ast.Case(c.caseTypes(), c.binding(), rename(c.body(), inner, substDenotes, fnParams, at),
                            c.unwrapAsserts(), at(at, c.pos())));
                }
                yield new Ast.Match(rename(m.scrutinee(), subst, substDenotes, fnParams, at), cases, at(at, m.pos()));
            }
            case Ast.If iff -> new Ast.If(rename(iff.cond(), subst, substDenotes, fnParams, at), rename(iff.then(), subst, substDenotes, fnParams, at), rename(iff.els(), subst, substDenotes, fnParams, at), at(at, iff.pos()));
            // the binder shadows in the success branch alone, so it is dropped from the substitution
            // there and left standing over the construction and the else value
            case Ast.IfConstructed ic -> new Ast.IfConstructed(
                    rename(ic.construct(), subst, substDenotes, fnParams, at), ic.binder(),
                    rename(ic.then(), without(subst, ic.binder()), substDenotes, fnParams, at),
                    Ast.mapArms(ic.els(), body -> rename(body, subst, substDenotes, fnParams, at)),
                    at(at, ic.pos()));
            case Ast.LetIn li -> {
                Ast.Expr value = rename(li.value(), subst, substDenotes, fnParams, at);
                Ast.Expr body = rename(li.body(), without(subst, li.name()), substDenotes, fnParams, at);
                yield new Ast.LetIn(li.name(), value, li.declaredType(), li.annotated(), li.opens(), body, at(at, li.pos()));
            }
            case Ast.ListLit lit -> new Ast.ListLit(renameList(lit.elements(), subst, substDenotes, fnParams, at), at(at, lit.pos()));
            case Ast.Tuple tup -> new Ast.Tuple(renameList(tup.elements(), subst, substDenotes, fnParams, at), at(at, tup.pos()));
            case Ast.TupleGet tg -> new Ast.TupleGet(rename(tg.tuple(), subst, substDenotes, fnParams, at), tg.index(), tg.arity(), at(at, tg.pos()));
            case Ast.ListComp comp -> new Ast.ListComp(rename(comp.element(), subst, substDenotes, fnParams, at), renameList(comp.guards(), subst, substDenotes, fnParams, at), at(at, comp.pos()));
            case Ast.Block block -> {
                // α-rename the block's own parameters to fresh `$`-names. Caller code — a lambda passed
                // to a function parameter — is spliced into this block's scope during inlining; if the
                // block bound a plain name (`acc`/`x`, as the derived combinators do) it would capture a
                // caller variable of the same name. Fresh `$`-names cannot collide with caller code.
                Map<String, String> inner = subst;
                List<String> freshParams = new ArrayList<>();
                for (String p : block.params()) {
                    String fresh = "$b" + (counter++) + "_" + p;
                    freshParams.add(fresh);
                    inner = with(inner, p, fresh);
                }
                yield new Ast.Block(freshParams, rename(block.body(), inner, substDenotes, fnParams, at), at(at, block.pos()));
            }
            case Ast.IntLit _ -> e;
            case Ast.DecimalLit _ -> e;
            case Ast.StringLit _ -> e;
            case Ast.BoolLit _ -> e;
            // it names nothing, so a substitution has nothing to rewrite in it
            case Ast.Unreachable _ -> e;
        };
    }

    /** The position to stamp on a rebuilt node: the override {@code at} for a prelude helper, or the
     * node's own position when {@code at} is null (a module-own helper keeps its positions). */
    private static SourcePos at(SourcePos at, SourcePos own) {
        return at != null ? at : own;
    }

    private List<Ast.Expr> renameList(List<Ast.Expr> es, Map<String, String> subst,
                                      Map<String, ValueName> substDenotes,
                                      Set<String> fnParams, SourcePos at) {
        List<Ast.Expr> out = new ArrayList<>();
        for (Ast.Expr e : es) {
            out.add(rename(e, subst, substDenotes, fnParams, at));
        }
        return out;
    }

    private static Map<String, String> without(Map<String, String> subst, String name) {
        if (!subst.containsKey(name)) {
            return subst;
        }
        Map<String, String> copy = new HashMap<>(subst);
        copy.remove(name);
        return copy;
    }

    /** {@code subst} with {@code name} rebound to {@code fresh} (a copy; the original is untouched). */
    private static Map<String, String> with(Map<String, String> subst, String name, String fresh) {
        Map<String, String> copy = new HashMap<>(subst);
        copy.put(name, fresh);
        return copy;
    }

    /** Records the module's own helpers that lie on a call cycle (self or mutual). A recursive helper
     * is lowered to a method that may call itself, rather than inlined (spec 13.1). A helper is
     * recursive iff it can reach itself through helper calls; every member of a mutual cycle is
     * reached from itself, so all are marked. */
    private void classifyRecursion() {
        // Both a module's own helpers and the shipped prelude helpers are scanned: `souther.list`'s
        // `foldFrom` is a recursive prelude helper, and it must be left standing (lowered to a method,
        // not inlined) exactly as a module-own recursive helper is, or the inliner would expand its
        // self-call forever.
        for (Map.Entry<String, Ast.FnDef> e : helpers.entrySet()) {
            Set<String> called = new HashSet<>();
            collectHelperCalls(e.getValue().body(), called);
            callsOf.put(e.getKey(), called);
        }
        for (String name : helpers.keySet()) {
            if (reaches(name, name, new HashSet<>())) {
                recursive.add(name);
            }
        }
    }

    /**
     * A value that reaches itself has nothing to be substituted with, so it is refused here, naming
     * the path it goes round.
     *
     * <p>The value graph is not the call graph. A helper on a call cycle is lowered to a method and
     * recurses at run time (ADR-0038); a value has no such form, so a cycle that passes through one is
     * an error however it is closed — by naming a value, or by calling a helper that names it. The two
     * are reported apart: a value cycle sent through the recursion check would be told to declare a
     * return type it never wrote.
     */
    private void rejectValueCycles() {
        Map<String, Set<String>> edges = new LinkedHashMap<>();
        for (Map.Entry<String, Ast.FnDef> e : own.entrySet()) {
            Set<String> out = new LinkedHashSet<>(callsOf.getOrDefault(e.getKey(), Set.of()));
            collectValueRefs(e.getValue().body(), out);
            edges.put(e.getKey(), out);
        }
        for (Map.Entry<String, Ast.FnDef> e : own.entrySet()) {
            if (!e.getValue().params().isEmpty()) {
                continue;   // a helper's own recursion is the call graph's business
            }
            // A value stands for a value. A block written as one — a `.field` getter, whose parameter
            // the compiler synthesizes — is refused where it is written rather than where it is used.
            if (e.getValue().body() instanceof Ast.Block block) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.block.notvalue").title("check.block.title")
                                .at(block.pos()).build(),
                        "a block is not a value: `let " + e.getKey() + "` writes no parameters, so it"
                                + " defines a value, and a block cannot be one (spec 12.5)");
            }
            List<String> path = new ArrayList<>();
            if (pathBackTo(e.getKey(), e.getKey(), edges, new LinkedHashSet<>(), path)) {
                path.add(0, e.getKey());
                String written = String.join(" -> ", path);
                throw CompileException.of(
                        Diagnostic.of(null, "check.value.cycle").title("check.value.cycle.title")
                                .at(e.getValue().pos(), e.getKey().length())
                                .args(e.getKey(), written).build(),
                        "`let " + e.getKey() + "` is defined in terms of itself (" + written + ")");
            }
        }
    }

    /**
     * The value a spread copies, or null where it copies something else — a parameter, a binding, or
     * a name that merely shares a value's spelling.
     *
     * <p>The spread carries what it resolved to, so this asks that rather than matching the spelling
     * against the module's definitions: a binding in force wins over a declaration, and a spread is
     * no exception.
     */
    private Ast.FnDef valueSpread(Ast.ValueRef spread) {
        if (!(spread.denotes() instanceof ValueName.Helper)) {
            return null;
        }
        // by the name it is reached by here, which for another module's value is the qualified one
        String reached = spread.written();
        Ast.FnDef value = own.get(reached);
        return value == null || !value.params().isEmpty() || value.body() == null
                || recursive.contains(reached) ? null : value;
    }

    /** The names of this module's values that {@code e} reads. A value is written bare, so a
     * reference to one is a {@code Var} and never reaches the call graph. */
    private void collectValueRefs(Ast.Expr e, Set<String> out) {
        if (e == null) {
            return;
        }
        if (e instanceof Ast.Var v && v.denotes() instanceof ValueName.Helper) {
            Ast.FnDef d = own.get(v.name());
            if (d != null && d.params().isEmpty()) {
                out.add(v.name());
            }
        }
        if (e instanceof Ast.NewData nd) {
            for (Ast.ValueRef spread : nd.spreads()) {
                if (valueSpread(spread) != null) {
                    out.add(spread.written());   // `...base` reads the value a bare name does
                }
            }
        }
        forEachChild(e, c -> collectValueRefs(c, out));
    }

    /** Records into {@code path} a route from {@code from} back to {@code target}, or answers false. */
    private boolean pathBackTo(String from, String target, Map<String, Set<String>> edges,
                               Set<String> seen, List<String> path) {
        for (String next : edges.getOrDefault(from, Set.of())) {
            path.add(next);
            if (next.equals(target)) {
                return true;
            }
            if (seen.add(next) && pathBackTo(next, target, edges, seen, path)) {
                return true;
            }
            path.remove(path.size() - 1);
        }
        return false;
    }

    /** Which helpers each helper's body calls. Built once, before the cycle search: {@link #reaches}
     * walks this graph from every helper, so scanning a body per edge scanned the shipped prelude —
     * a few hundred call sites — once per path through it rather than once. */
    private final Map<String, Set<String>> callsOf = new HashMap<>();

    /** Whether {@code target} is reachable from {@code from} through helper-call edges. Prelude
     * helpers never call a module's own helpers, so a cycle stays within the module's own helpers. */
    private boolean reaches(String from, String target, Set<String> seen) {
        Set<String> called = callsOf.get(from);
        if (called == null) {
            return false;
        }
        for (String c : called) {
            if (c.equals(target)) {
                return true;
            }
            if (seen.add(c) && reaches(c, target, seen)) {
                return true;
            }
        }
        return false;
    }

    /** Whether {@code name} occurs as a variable or a call target anywhere in {@code e}. Used to
     * spot a self-referencing lambda and to tell whether a let-bound lambda escapes (is used as a
     * value) after its applications have been expanded away. */
    private static boolean mentions(Ast.Expr e, String name) {
        if (e instanceof Ast.Var v && v.name().equals(name)) {
            return true;
        }
        if (e instanceof Ast.Call c && c.fn().equals(name)) {
            return true;
        }
        boolean[] found = {false};
        forEachChild(e, child -> found[0] |= mentions(child, name));
        return found[0];
    }

    private void collectHelperCalls(Ast.Expr e, Set<String> out) {
        // Applying a function-typed parameter, or a binding holding a function, is not a call to
        // whatever else bears that name. The call carries what it resolved to, so it is asked rather
        // than matched against the helper table — a parameter named like a helper was reaching the
        // graph as a call to that helper, which made `let f (g: (Int) -> Int) = g(1)` recursive. A
        // call that resolved to nothing keeps the table's answer: the prelude's own bodies are read
        // here before their names have been through resolution.
        if (e instanceof Ast.Call call && !(call.denotes() instanceof ValueName.Local)) {
            // `List.fold` desugars to `List.foldFrom` before inlining, so a body that folds reaches the
            // recursive `foldFrom` — recursion classification and prelude-injection must see that.
            String fn = call.fn().equals("List.fold") ? "List.foldFrom" : call.fn();
            if (helpers.containsKey(fn)) {
                out.add(fn);
            }
        }
        forEachChild(e, c -> collectHelperCalls(c, out));
    }

    /** Applies {@code f} to every direct subexpression of {@code e}; the one exhaustive walk
     * lives on the AST, so a node kind added later cannot be skipped here unnoticed. */
    private static void forEachChild(Ast.Expr e, java.util.function.Consumer<Ast.Expr> f) {
        Ast.forEachChild(e, f);
    }
}
