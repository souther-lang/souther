package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.Type;
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
import java.util.OptionalInt;
import java.util.Set;
import java.util.function.IntFunction;
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

    /** The module whose bodies this expands into. A binding an expansion makes belongs to a
     * definition of this module, which is what tells it from the same helper expanded elsewhere. */
    private final String module;
    private final Map<String, Ast.FnDef> helpers;   // prelude + module-own, by the name they are reached by
    private final Map<String, Ast.FnDef> own;       // the module's own helpers (standalone check)
    /**
     * The lambdas this pass expands as helpers, each under the binding it is bound to: a lambda a
     * block's {@code let} binds, and a lambda handed to a function parameter.
     *
     * <p>Apart from {@link #helpers} because they are apart: a declaration is reached by a name, a
     * lambda is reached by a binding. Held together, a lambda bound to {@code f} took the place of a
     * declared {@code f} for as long as it was in scope, which is why applying it had to be told from
     * applying the declaration by a spelling and why a lambda naming itself had to be refused.
     */
    private final Map<BindingId, Ast.FnDef> scopedLambdas = new HashMap<>();
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
    private final Set<String> recursive = new HashSet<>();   // own helpers on a call cycle (spec 13.1)
    /** Where a lambda given to a function parameter was written, by the binding it was registered
     * under. Asked by the binding and not by the spelling: two combinators nested one inside the
     * other give their function parameters the same name as often as not, and a report that found
     * the outer one's lambda would point at another author's line. */
    private final Map<BindingId, LambdaOrigin> lambdaOrigins = new HashMap<>();
    private int counter = 0;
    /** The body being expanded, and the bindings this expansion introduces into it. An expansion
     * writes bindings no source wrote, so they belong to it rather than to the definition whose text
     * it is splicing, which is what keeps two copies of one helper's body apart. */
    private Ast.Binders binders;
    /** The body being expanded into, which the copies of a helper's bindings belong under. */
    private BindingOwner into;

    /** Where a lambda given to a function parameter was written: the parameter it fills, the helper
     * that declares that parameter, and the lambda's own position. The lambda is inlined under a
     * synthetic name, which is a spelling and must never reach a diagnostic — an error about it is
     * reported against these instead. */
    private record LambdaOrigin(String param, String owner, SourcePos pos) {}

    private HelperInliner(String module, Map<String, Ast.FnDef> helpers, Map<String, Ast.FnDef> own) {
        this.module = module;
        this.helpers = helpers;
        this.own = own;
    }

    /** The body of {@code fn} in this module — what an expansion written into it belongs to. */
    public BindingOwner bodyOf(String fn) {
        return new BindingOwner.OfValue(module, fn);
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
        HelperInliner inliner = new HelperInliner(module.name(), withPrelude(table),
                new LinkedHashMap<>(own));
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
    public static HelperInliner forHelpers(String module, Map<String, Ast.FnDef> own,
                                           Map<String, Ast.FnDef> imported, InliningPolicy policy) {
        // In the order they are written, so a module with two helpers to complain about complains
        // about the earlier one first.
        Map<String, Ast.FnDef> joined = new LinkedHashMap<>(imported);
        joined.putAll(own);
        Map<String, Ast.FnDef> table = policy == InliningPolicy.FULL
                ? withPrelude(joined) : joined;
        HelperInliner inliner = new HelperInliner(module, table, new LinkedHashMap<>(own));
        inliner.classifyRecursion();
        inliner.rejectValueCycles();
        return inliner;
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
            collectHelperCalls(fn.written(), reachable);
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
        HelperInliner reader = new HelperInliner(module.name(), table, table);
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
            reader.collectValueNames(e, named);
            for (String value : named) {
                Ast.FnDef def = table.get(value);
                if (def != null && def.params().isEmpty()
                        && def.body() instanceof Ast.FnBody.Written w
                        && valuesRead.add(value)) {
                    work.add(w.expr());
                }
            }
        }
        Set<String> out = new LinkedHashSet<>();
        for (String name : called) {
            Ast.FnDef helper = table.get(name);
            if (helper != null && helper.body() instanceof Ast.FnBody.Written w
                    && !helper.params().isEmpty() && !Elaborator.producesFunction(w.expr())) {
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
            out.put(name, new Ast.FnDef(name, def.params(), def.declaredReturn(),
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
                    def.body(), def.partial(), def.pos()));
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
        Ast.Expr closed = recursive.contains(fn.name())
                ? inlineRecursiveBody(fn) : inline(fn.written(), bodyOf(fn.name()));
        return new Ast.FnDef(qualified(module, fn.name()), fn.params(), fn.declaredReturn(),
                new Ast.FnBody.Written(publishedBy(qualifyHelpersOf(closed, module), module)),
                fn.partial(), fn.pos());
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
        // a spread names a value, and a value is not a construction: what it built was built where it
        // was defined, so the mark is already on it
        Ast.Expr rebuilt = Ast.mapChildren(e, c -> publishedBy(c, module), s -> s);
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
        Ast.Expr rebuilt = Ast.mapChildren(e, HelperInliner::carriedByValue, s -> s);
        return switch (rebuilt) {
            case Ast.NewData nd -> nd.carriedByValue();
            case Ast.Var v when v.denotes() instanceof ValueName.OfType named ->
                    v.denoting(named.carriedByValue());
            case Ast.Apply call -> call.carriedByValue();
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
            fns.add(fn.body() instanceof Ast.FnBody.Written w
                    ? new Ast.FnDef(fn.name(), fn.params(), fn.declaredReturn(),
                            new Ast.FnBody.Written(qualifyForeign(w.expr(), m.name())),
                            fn.partial(), fn.pos())
                    : fn);
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
        // a name slot takes the same rewrite as a name standing on its own: a spread names a value
        // the way any other position does
        Ast.Expr rebuilt = Ast.mapChildren(e, c -> qualifyHelpers(c, which),
                s -> qualified(s, which));
        return switch (rebuilt) {
            case Ast.Apply call when foreign(call.denotes(), which) ->
                    new Ast.Apply(qualifiedName(call.denotes()), call.denotes(), call.args(),
                            call.origin(),
                            call.pos());
            case Ast.Var v -> qualified(v, which);
            default -> rebuilt;
        };
    }

    /** {@code name} written qualified where it denotes a helper {@code which} accepts. */
    private static Ast.Var qualified(Ast.Var name, Predicate<ValueName.Helper> which) {
        return foreign(name.denotes(), which)
                ? new Ast.Var(qualifiedName(name.denotes()), name.denotes(), name.pos())
                : name;
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
            case Ast.Apply call -> call.denotes();
            case Ast.Var v -> v.denotes();
            default -> null;
        };
        if (denotes instanceof ValueName.Helper helper) {
            out.add(helper);
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
                forHelpers(m.name(), helpersOf(settled), published, InliningPolicy.DISCHARGE);
        Map<TypeName, List<Ast.InvariantClause>> out = new LinkedHashMap<>();
        for (Ast.Def def : settled.defs()) {
            if (def instanceof Ast.Data d && !d.invariants().isEmpty()) {
                TypeName declared = new TypeName(m.name(), d.name());
                out.put(declared, Ast.mapClauses(d.invariants(),
                        clause -> inliner.inline(clause, new BindingOwner.OfData(declared))));
            }
        }
        return out;
    }

    Ast.Module withInlinedInvariants(Ast.Module m) {
        List<Ast.Def> defs = new ArrayList<>();
        for (Ast.Def def : m.defs()) {
            if (def instanceof Ast.Data d && !d.invariants().isEmpty()) {
                BindingOwner declared = new BindingOwner.OfData(new TypeName(m.name(), d.name()));
                defs.add(new Ast.Data(d.name(), d.newtype(), d.includes(), d.fields(),
                        Ast.mapClauses(d.invariants(), clause -> inline(clause, declared)),
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

    /** The declaration reached by {@code name} across the prelude and the module's own helpers, or
     * null where the name reaches none. For a reader walking a set of names this pass answered with —
     * the recursive helpers, say. A reader holding a call asks {@link #applied} instead, because what
     * a call applies is not decided by how it is spelled. */
    public Ast.FnDef helper(String name) {
        return helpers.get(name);
    }

    /** The body {@code call} applies, or null where it applies something no body stands behind. */
    public Ast.FnDef applied(Ast.Apply call) {
        return appliedHelper(call);
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
    private static Ast.Apply desugarFold(Ast.Apply call) {
        if (!"List.fold".equals(call.reaches()) || call.args().size() != 3) {
            return call;
        }
        List<Ast.Expr> args = new ArrayList<>(call.args());
        args.add(new Ast.IntLit(0, call.pos()));
        return new Ast.Apply("List.foldFrom", new ValueName.Stdlib("List.foldFrom"), args,
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
            return inline(h.written(), bodyOf(h.name()));
        } finally {
            helpers.putAll(shadowed);
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
     * Map.upsert}'s {@code Map<'k, 'a>}) says nothing concrete at a call site, so it is not carried —
     * the caller's own arguments are what fix those variables. */
    private static boolean mentionsRetTypeVar(Ast.RetType ret) {
        return ret != null && ret.cases().stream().anyMatch(HelperInliner::mentionsTypeVar);
    }

    /**
     * Asked of what the reference denotes, not of how it was spelled. A reference a
     * helper's own settling wrote carries its type and no surface text at all
     * ({@link Ast.TypeRef#of}), so reading the spelling answers no about every one of them.
     */
    static boolean mentionsTypeVar(Ast.TypeTerm term) {
        if (term instanceof Ast.FnType fn) {
            return fn.params().stream().anyMatch(HelperInliner::mentionsRetTypeVar)
                    || mentionsRetTypeVar(fn.result());
        }
        if (!(term instanceof Ast.TypeRef ref)) {
            return false;
        }
        if (ref.denotes() != null) {
            return Type.mentions(ref.denotes(), t -> t instanceof Type.Var);
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
    private List<Ast.FnParam> declaredParams(Ast.Apply call) {
        if ("List.fold".equals(call.reaches()) && call.args().size() == 3) {
            Ast.FnDef foldFrom = helpers.get("List.foldFrom");
            return foldFrom == null ? null : foldFrom.params().subList(0, 3);
        }
        Ast.FnDef helper = helpers.get(call.reaches());
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
                throw CompileException.of(
                        Diagnostic.of(null, "check.fn.argnotfn").title("check.fn.title")
                                .at(lambda.pos()).args(call.written(), i + 1, param).build(),
                        "argument " + (i + 1) + " of `" + call.written() + "` is `" + param
                                + "`, which does not take a function");
            }
            String shape = params.stream().map(Ast.FnParam::name)
                    .collect(java.util.stream.Collectors.joining(", "));
            throw CompileException.of(
                    Diagnostic.of(null, "check.fn.argorder").title("check.fn.title")
                            .at(lambda.pos())
                            .args(call.written(), i + 1, param, fnParam + 1, params.get(fnParam).name(), shape)
                            .hint("check.fn.argorder.hint").build(),
                    "argument " + (i + 1) + " of `" + call.written() + "` is `" + param
                            + "`, which does not take a function: the function goes to argument "
                            + (fnParam + 1) + " (`" + params.get(fnParam).name() + "`). Write `"
                            + call.written() + "(" + shape + ")`.");
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
            case ValueName.Local local -> scopedLambdas.get(local.id());
            case ValueName.Helper _, ValueName.Stdlib _ -> helpers.get(reachedBy);
            // a construction, an injected behavior, `None`, or a name that denotes nothing: each is
            // applied by something other than an expansion, and each is reported where it belongs
            case ValueName.OfType _, ValueName.Behavior _, ValueName.Builtin _,
                    ValueName.Unresolved _ -> null;
        };
    }

    /**
     * The arguments of a call that stays a call, with a dependency handed over by name replaced by
     * the block that forwards to it: {@code depth(code, fetch)} becomes {@code depth(code, (c) ->
     * fetch(c))}, which spec §blocks says is the same thing.
     *
     * <p>Where the callee is expanded the two already are the same thing — the expansion substitutes
     * the argument's name into the parameter's applications, so the name only ever stands in a call.
     * A recursive helper is lowered to a method instead (spec 13.1), which leaves the argument
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
        if (callee == null || dependencies.isEmpty()) {
            return args;
        }
        List<Ast.Expr> out = new ArrayList<>(args);
        for (int i = 0; i < callee.params().size() && i < out.size(); i++) {
            Ast.RetType declared = callee.params().get(i).type();
            Ast.FnType want = declared == null ? null : declared.asFn();
            if (want == null || !(out.get(i) instanceof Ast.Var v)
                    || !(v.denotes() instanceof ValueName.Local local)
                    || !dependencies.contains(local.id())) {
                continue;
            }
            out.set(i, etaExpand(v, want.params().size(), _ -> "$" + counter++ + "_" + v.name()));
        }
        return out;
    }

    /** Which bindings the {@code depends on} parameters of the behavior {@code let} being expanded
     * are. Empty while expanding anything else: only a behavior's {@code let} has them
     * (spec §depends-on). */
    private Set<BindingId> dependencies = Set.of();

    /** As {@link #inline(Ast.Expr)}, for the body of a behavior {@code let} whose {@code depends on}
     * parameters are bound at {@code binders}. */
    public Ast.Expr inline(Ast.Expr e, Set<BindingId> dependencies, BindingOwner into) {
        Set<BindingId> outer = this.dependencies;
        this.dependencies = dependencies;
        try {
            return inline(e, into);
        } finally {
            this.dependencies = outer;
        }
    }

    /**
     * Rewrites every helper call in {@code e} to its inlined body, into {@code into}.
     *
     * <p>{@code into} is the body being written: the bindings an expansion introduces belong to it,
     * so two copies of one helper's body spliced into two definitions do not answer as one binding.
     */
    public Ast.Expr inline(Ast.Expr e, BindingOwner into) {
        Ast.Binders outerBinders = binders;
        BindingOwner outerInto = this.into;
        this.into = into;
        binders = new Ast.Binders(new BindingOwner.Synthesized(into, BindingOwner.Pass.INLINER, 0));
        try {
            return inline(e);
        } finally {
            binders = outerBinders;
            this.into = outerInto;
        }
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

    /** Rewrites every helper call in {@code e} to its inlined body, into the body already named. */
    public Ast.Expr inline(Ast.Expr e) {
        if (binders == null) {
            throw new IllegalStateException("nothing said which body this expansion is written into");
        }
        return switch (e) {
            // Applying something other than a name. The applied expression is bound first and the
            // application reads the binding, which is the shape every reader downstream already has
            // — and which says outright what the order is: the function is worked out once, before
            // any argument, and the binding is what is applied.
            case Ast.Apply raw when !raw.appliesAName() -> {
                Ast.Binder f = binders.binder("$fn" + counter++, raw.function().pos());
                // What the application reaches is the binding, and what a report about it quotes is
                // what the author wrote — a field read applied (`deps.count(x)`) has a spelling, and
                // quoting the binding would name `$fn0`, which is nowhere in the source. The two are
                // separate slots: the binding is in the callee position, the spelling beside it.
                yield inline(new Ast.LetIn(f, raw.function(), null, false, null,
                        new Ast.Apply(new Ast.Var(f.name(), new ValueName.Local(f.name(), f.id()),
                                raw.pos()),
                                raw.args(), raw.origin(), spelling(raw.function()), raw.pos()),
                        raw.pos()));
            }
            case Ast.Apply rawCall -> {
                checkFunctionArgumentPlacement(rawCall);
                Ast.Apply call = desugarNamedBlock(desugarFold(rawCall));
                List<Ast.Expr> args = new ArrayList<>();
                for (Ast.Expr a : call.args()) {
                    args.add(inline(a));
                }
                Ast.FnDef helper = appliedHelper(call);
                // a recursive helper is reached by the name it is declared under; a lambda a binding
                // holds is not one, whatever it is called
                boolean standing = !(call.denotes() instanceof ValueName.Local)
                        && recursive.contains(call.reaches());
                if (helper == null || standing) {
                    // builtin, injected behavior, a function-typed parameter, or a recursive helper —
                    // a recursive helper is lowered to a method, so its call stays a Call (spec 13.1);
                    // only its args inline.
                    yield call.withArgs(forwardDependencies(helper, args));
                }
                // A declaration written with no parameter list is a value ([#fn-declaration]), so
                // applying it applies whatever function that value is — not the declaration, which
                // takes nothing. The value is substituted and the arguments are applied to it.
                if (helper.params().isEmpty() && !args.isEmpty()
                        && call.function() instanceof Ast.Var named) {
                    yield inline(new Ast.Apply(valueOf(named), args, call.origin(), call.pos()));
                }
                if (args.size() != helper.params().size()) {
                    LambdaOrigin origin = call.denotes() instanceof ValueName.Local applied
                            ? lambdaOrigins.get(applied.id()) : null;
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
                                    .at(call.pos(), call.written().length())
                                    .args(helper.name(), helper.params().size(), args.size()).build(),
                            "helper `let " + helper.name() + "` takes " + helper.params().size()
                                    + " argument(s) but is called with " + args.size());
                }
                // Everything this expansion writes belongs to it: the bindings its arguments become,
                // the one a lambda given to a function parameter is registered under, the one its
                // declared return is carried on, and every binding copied out of the callee's body.
                // One minter, so no two of them are the same binding, and a reader can ask of any of
                // them which call it came from.
                BindingOwner mine = new BindingOwner.Expansion(into, call.denotes(), counter++);
                Ast.Binders ours = new Ast.Binders(mine);
                // What the callee's signature leaves open, this call decides. Its variables are
                // instantiated once, here, over the whole signature at once — so a variable it wrote
                // in two of its parameters is one variable in what this expansion writes, and two
                // calls of it decide separately. Splitting the signature into a binding per parameter
                // is what would otherwise lose that: each binding's type would be read on its own,
                // and nothing left afterwards says the two came from one application.
                Map<String, Type> applied = instantiation(helper, mine);
                Map<BindingId, String> subst = new HashMap<>();
                // what each substituted callee resolved to at the call site, so the expansion carries
                // the argument's own answer rather than deciding one for it
                Map<BindingId, ValueName> substDenotes = new HashMap<>();
                List<BindingId> scoped = new ArrayList<>();   // the lambdas given to fn params
                List<Ast.Bound> bound = new ArrayList<>();
                List<Ast.Given> given = new ArrayList<>();
                for (int i = 0; i < helper.params().size(); i++) {
                    Ast.FnParam p = helper.params().get(i);
                    Ast.Expr arg = args.get(i);
                    if (p.type() != null && p.type().asFn() != null) {
                        // a function argument is not a value, so it cannot be bound to a let. A named
                        // function is substituted directly (f(x) becomes inc(x)); a lambda is
                        // registered under a fresh name as a scoped helper, so each application of the
                        // parameter β-reduces to the lambda's body, as a let-bound lambda does (spec 12.5).
                        // Asked of the callee as written, not of what it expanded to: applying a
                        // function parameter is what removes it, because the application β-reduces
                        // to the lambda's body, so the expansion holds no reference either way.
                        given.add(new Ast.Given(instantiated(p.type(), applied), arg,
                                references(helper.written(), p.binder().id())));
                        if (arg instanceof Ast.Var fnName) {
                            subst.put(p.binder().id(), fnName.name());
                            substDenotes.put(p.binder().id(), fnName.denotes());
                        } else if (arg instanceof Ast.Block lambda) {
                            Ast.Binder f = ours.binder("$" + p.name(), lambda.pos());
                            subst.put(p.binder().id(), f.name());
                            substDenotes.put(p.binder().id(), new ValueName.Local(f.name(), f.id()));
                            scoped.add(f.id());
                            // The lambda is registered under what the callee declared of the
                            // parameter it was given to, this application's variables written in. So
                            // where the callee applies it, that application expands like any other
                            // call and is read against the signature there — in the one place the
                            // types this application decided are in force. Registering it bare is
                            // what used to throw the signature away at the point it was reduced,
                            // leaving nothing between the caller's function and what was declared of
                            // it (issues #318, #320).
                            Ast.FnType declares = declaredFn(p.type(), applied);
                            List<Ast.FnParam> lparams = new ArrayList<>();
                            for (int lp = 0; lp < lambda.params().size(); lp++) {
                                lparams.add(new Ast.FnParam(lambda.params().get(lp),
                                        declares == null || lp >= declares.params().size() ? null
                                                : declares.params().get(lp)));
                            }
                            // the lambda's body is caller code, so it is not renamed by this helper's
                            // substitution — only the enclosing helper body is.
                            scopedLambdas.put(f.id(),
                                    new Ast.FnDef(f.name(), lparams,
                                            declares == null ? null : declares.result(),
                                            new Ast.FnBody.Written(lambda.body()), lambda.pos()));
                            lambdaOrigins.put(f.id(), new LambdaOrigin(p.name(), helper.name(), lambda.pos()));
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
                                    .args(rawCall.written(), i + 1, p.name(), shape);
                            if (shape != null) {
                                d.hint("check.fn.argnotvalue.hint");
                            }
                            throw CompileException.of(d.build(),
                                    "argument " + (i + 1) + " of `" + rawCall.written() + "` is `" + p.name()
                                            + "`, which takes a function: pass a named function or a lambda"
                                            + (shape == null ? ""
                                                    : ". Write `" + rawCall.written() + "(" + shape + ")`."));
                        }
                    } else {
                        // the binding the argument is bound to; the reads of the parameter inside the
                        // body are answered with it, so a read says which binding it is rather than
                        // where it happens to be written
                        Ast.Binder f = ours.binder(p.name(), call.pos());
                        subst.put(p.binder().id(), f.name());
                        substDenotes.put(p.binder().id(), new ValueName.Local(f.name(), f.id()));
                        // carry the parameter's declared type onto the binding, so a value known to
                        // be a sum (an annotated `s: S`) is not narrowed to the argument's specific
                        // case when the body is re-checked inline — a `match s` inside still sees S.
                        bound.add(new Ast.Bound(f, instantiated(p.type(), applied), arg));
                    }
                }
                // a prelude helper's body is stamped with the call site, so errors inside it point at
                // the user's call, not at the shipped source of souther.*
                SourcePos at = keepsItsPositions(call) ? null : call.pos();
                Copy copy = new Copy(helper.written(), ours);
                Ast.Expr body = inline(rename(helper.written(), subst, substDenotes, at, copy));   // expand nested helpers too
                scoped.forEach(scopedLambdas::remove);
                scoped.forEach(lambdaOrigins::remove);
                yield new Ast.Expansion(call.denotes(), mine, bound, given,
                        instantiated(helper.declaredReturn(), applied), body, call.pos());
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
            // Already expanded. Its body may still hold calls of its own — a helper whose callee was
            // not in the table when this ran the first time — so it is walked like any other.
            case Ast.Expansion ex -> {
                List<Ast.Bound> bound = new ArrayList<>();
                for (Ast.Bound b : ex.bound()) {
                    bound.add(new Ast.Bound(b.binder(), b.declaredType(), inline(b.value())));
                }
                List<Ast.Given> given = new ArrayList<>();
                for (Ast.Given g : ex.given()) {
                    given.add(new Ast.Given(g.declaredType(), inline(g.value()), g.applied()));
                }
                yield new Ast.Expansion(ex.callee(), ex.application(), bound, given,
                        ex.declaredReturn(), inline(ex.body()), ex.pos());
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
                    scopedLambdas.put(alias, aliased);
                    Ast.Expr aliasBody = inline(li.body());
                    scopedLambdas.remove(alias);
                    yield references(aliasBody, alias)
                            ? new Ast.LetIn(li.binder(), value, li.declaredType(), li.annotated(),
                                    li.opens(), aliasBody, li.pos())
                            : aliasBody;
                }
                if (!(value instanceof Ast.Block lambda)) {
                    yield new Ast.LetIn(li.binder(), value, li.declaredType(), li.annotated(),
                            li.opens(), inline(li.body()), li.pos());
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
                scopedLambdas.put(bound,
                        new Ast.FnDef(li.name(), params, null,
                                new Ast.FnBody.Written(lambda.body()), li.pos()));
                Ast.Expr body = inline(li.body());
                scopedLambdas.remove(bound);
                // if the binding is still read, the function was used as a value, not just applied —
                // it escapes, which needs a runtime closure. Keep the binding so the check that
                // reports an escaping block sees it.
                yield references(body, bound)
                        ? new Ast.LetIn(li.binder(), lambda, li.declaredType(), li.annotated(),
                                li.opens(), body, li.pos())
                        : body;
            }
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
            Ast.Binder p = binders.binder(binderName.apply(i), function.pos());
            params.add(p);
            args.add(Ast.Var.local(p, function.pos()));
        }
        return new Ast.Block(params,
                new Ast.Apply(function.name(), function.denotes(), args, ConstructionOrigin.own(),
                        function.pos()),
                function.pos());
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
        int arity = switch (v.denotes()) {
            case ValueName.Stdlib lib -> {
                Prelude.PreludeEntry entry = Prelude.entry(lib.qualified());
                Ast.FnDef declared = entry == null ? null : entry.declaration();
                yield declared == null ? 0 : declared.params().size();
            }
            case ValueName.Helper _ -> {
                Ast.FnDef declared = helpers.get(v.reaches());
                yield declared == null || declared.body() == null ? 0 : declared.params().size();
            }
            // A behavior's name handed over is the behavior: the block applies the behavior, so the
            // emitted code goes through the behavior's class and not through the `let` that
            // implements it. Only the ones a body may name are here — a behavior with a requirement
            // is a binding by the time it can be written.
            case ValueName.Behavior b -> callableBehaviors.getOrDefault(b.name(), 0);
            // A binding holds whatever it was given; a construction, a checker built-in and a name
            // that denotes nothing stand for no declaration at all.
            case ValueName.Local _, ValueName.OfType _, ValueName.Builtin _,
                    ValueName.Unresolved _ -> 0;
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
            int k = counter++;
            return inline(etaExpand(v, arity.getAsInt(), i -> "$v" + k + "_" + i));
        }
        if (!(v.denotes() instanceof ValueName.Helper)) {
            return v;
        }
        Ast.FnDef value = helpers.get(v.reaches());
        if (value == null || value.body() == null || recursive.contains(v.name())) {
            return v;
        }
        return carriedByValue(inline(value.written()));
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
            Ast.Binder name = binders.binder("$s" + counter++ + "_" + spread.bare(), spread.pos());
            bound.add(name);
            values.add(carriedByValue(inline(value.written())));
            spreads.add(Ast.Var.local(name, spread.pos()));
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
    private Ast.Apply desugarNamedBlock(Ast.Apply call) {
        Integer idx = BLOCK_ARG.get(call.reaches());
        if (idx == null || idx >= call.args().size()
                || !(call.args().get(idx) instanceof Ast.Var v)) {
            return call;
        }
        Ast.FnDef helper = expands(v.denotes(), v.reaches());
        if (helper == null) {
            return call;   // a bare name that stands for no body is left for the type checker to report
        }
        int k = counter++;
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

        /** This copy's binder for one the body has. */
        Ast.Binder of(Ast.Binder binder) {
            return new Ast.Binder.Bound(binder.name(), mine.get(binder.id()), binder.pos());
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
     * <p>{@code at}, when non-null, is stamped onto every rebuilt node in place of its own position.
     * A prelude helper is expanded with the call site as {@code at}, so a type error inside its body
     * points at the user's call — {@code filter(xs, x -> x * 2)} — not at a line of {@code souther.list}
     * the user never wrote. A module-own helper, and a lambda given to a fn parameter, pass {@code
     * null} and keep the positions their bodies have ({@link #keepsItsPositions}). The caller's
     * argument expressions, spliced in separately, keep their own positions either way.
     */
    private Ast.Expr rename(Ast.Expr e, Map<BindingId, String> subst,
                            Map<BindingId, ValueName> substDenotes, SourcePos at, Copy copy) {
        return switch (e) {
            case Ast.Var v -> renameVar(v, subst, substDenotes, at, copy);
            case Ast.FieldAccess fa -> new Ast.FieldAccess(rename(fa.target(), subst, substDenotes, at, copy), fa.field(), at(at, fa.pos()));
            // the callee is renamed as the expression it is, like every other subexpression. A name
            // applied is an `Ast.Var` held here, so it goes through the arm above and is substituted
            // exactly as a read of it would be — the position cannot ask a different question.
            case Ast.Apply call -> new Ast.Apply(
                    rename(call.function(), subst, substDenotes, at, copy),
                    renameList(call.args(), subst, substDenotes, at, copy),
                    call.origin(), call.appliedAs(), at(at, call.pos()));
            case Ast.Binary bin -> new Ast.Binary(bin.op(), rename(bin.left(), subst, substDenotes, at, copy), rename(bin.right(), subst, substDenotes, at, copy), at(at, bin.pos()));
            case Ast.Neg neg -> new Ast.Neg(rename(neg.operand(), subst, substDenotes, at, copy), at(at, neg.pos()));
            case Ast.NewData nd -> {
                List<Ast.FieldInit> inits = new ArrayList<>();
                for (Ast.FieldInit i : nd.inits()) {
                    inits.add(new Ast.FieldInit(i.name(), rename(i.value(), subst, substDenotes, at, copy), at(at, i.pos())));
                }
                // `..param` copies the renamed binding: a name slot asks what a name asks
                List<Ast.Var> spreads = new ArrayList<>();
                for (Ast.Var s : nd.spreads()) {
                    spreads.add(renameVar(s, subst, substDenotes, at, copy));
                }
                yield new Ast.NewData(nd.typeName(), inits, spreads, nd.origin(), at(at, nd.pos()));
            }
            case Ast.Match m -> {
                List<Ast.Case> cases = new ArrayList<>();
                for (Ast.Case c : m.cases()) {
                    cases.add(new Ast.Case(c.caseTypes(),
                            c.binding() == null ? null : copy.of(c.binding()),
                            rename(c.body(), subst, substDenotes, at, copy),
                            c.unwrapAsserts(), at(at, c.pos())));
                }
                yield new Ast.Match(rename(m.scrutinee(), subst, substDenotes, at, copy), cases, at(at, m.pos()));
            }
            case Ast.If iff -> new Ast.If(rename(iff.cond(), subst, substDenotes, at, copy), rename(iff.then(), subst, substDenotes, at, copy), rename(iff.els(), subst, substDenotes, at, copy), at(at, iff.pos()));
            // the success binder has its own BindingId, so a reference to it is not a candidate for
            // substitution, and neither the construction nor the else value can reach it
            case Ast.IfConstructed ic -> new Ast.IfConstructed(
                    rename(ic.construct(), subst, substDenotes, at, copy), copy.of(ic.binder()),
                    rename(ic.then(), subst, substDenotes, at, copy),
                    Ast.mapArms(ic.els(), body -> rename(body, subst, substDenotes, at, copy)),
                    at(at, ic.pos()));
            case Ast.LetIn li -> {
                Ast.Expr value = rename(li.value(), subst, substDenotes, at, copy);
                Ast.Expr body = rename(li.body(), subst, substDenotes, at, copy);
                yield new Ast.LetIn(copy.of(li.binder()), value, li.declaredType(), li.annotated(),
                        li.opens(), body, at(at, li.pos()));
            }
            // A body already expanded once, being copied into another caller. The signature comes
            // along as it stands: what its variables stand for is settled while each copy is typed,
            // from that copy's own arguments, so two copies decide separately without the variables
            // having to be minted again here.
            case Ast.Expansion ex -> {
                List<Ast.Bound> bound = new ArrayList<>();
                for (Ast.Bound b : ex.bound()) {
                    bound.add(new Ast.Bound(copy.of(b.binder()), b.declaredType(),
                            rename(b.value(), subst, substDenotes, at, copy)));
                }
                List<Ast.Given> given = new ArrayList<>();
                for (Ast.Given g : ex.given()) {
                    given.add(new Ast.Given(g.declaredType(),
                            rename(g.value(), subst, substDenotes, at, copy), g.applied()));
                }
                yield new Ast.Expansion(ex.callee(), ex.application(), bound, given,
                        ex.declaredReturn(), rename(ex.body(), subst, substDenotes, at, copy),
                        at(at, ex.pos()));
            }
            case Ast.ListLit lit -> new Ast.ListLit(renameList(lit.elements(), subst, substDenotes, at, copy), at(at, lit.pos()));
            case Ast.Tuple tup -> new Ast.Tuple(renameList(tup.elements(), subst, substDenotes, at, copy), at(at, tup.pos()));
            case Ast.TupleGet tg -> new Ast.TupleGet(rename(tg.tuple(), subst, substDenotes, at, copy), tg.index(), tg.arity(), at(at, tg.pos()));
            case Ast.ListComp comp -> new Ast.ListComp(rename(comp.element(), subst, substDenotes, at, copy), renameList(comp.guards(), subst, substDenotes, at, copy), at(at, comp.pos()));
            case Ast.Block block -> {
                List<Ast.Binder> params = new ArrayList<>();
                for (Ast.Binder p : block.params()) {
                    params.add(copy.of(p));
                }
                yield new Ast.Block(params,
                        rename(block.body(), subst, substDenotes, at, copy),
                        at(at, block.pos()));
            }
            case Ast.IntLit _ -> e;
            case Ast.DecimalLit _ -> e;
            case Ast.StringLit _ -> e;
            case Ast.BoolLit _ -> e;
            // it names nothing, so a substitution has nothing to rewrite in it
            case Ast.Unreachable _ -> e;
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
            case ValueName.Helper helper -> helper.module().equals(module);
            case ValueName.Stdlib _, ValueName.Behavior _, ValueName.OfType _,
                    ValueName.Builtin _, ValueName.Unresolved _ -> false;
        };
    }

    /** The position to stamp on a rebuilt node: the override {@code at} for a prelude helper, or the
     * node's own position when {@code at} is null (see {@link #keepsItsPositions}). */
    private static SourcePos at(SourcePos at, SourcePos own) {
        return at != null ? at : own;
    }

    /**
     * One name renamed — what {@link #rename} does wherever a name stands, whether that is an
     * expression of its own or the name a spread holds.
     *
     * <p>A substituted name keeps what the argument resolved to, so a named function handed to a
     * combinator stays the helper it is rather than becoming a binding of that spelling.
     */
    private Ast.Var renameVar(Ast.Var v, Map<BindingId, String> subst,
                              Map<BindingId, ValueName> substDenotes, SourcePos at, Copy copy) {
        return v.denotes() instanceof ValueName.Local p && subst.containsKey(p.id())
                ? new Ast.Var(subst.get(p.id()), substituted(substDenotes, p.id()), at(at, v.pos()))
                : new Ast.Var(v.name(), copy.of(v.denotes()), at(at, v.pos()));
    }

    private List<Ast.Expr> renameList(List<Ast.Expr> es, Map<BindingId, String> subst,
                                      Map<BindingId, ValueName> substDenotes,
                                      SourcePos at, Copy copy) {
        List<Ast.Expr> out = new ArrayList<>();
        for (Ast.Expr e : es) {
            out.add(rename(e, subst, substDenotes, at, copy));
        }
        return out;
    }

    /**
     * What this expansion substituted for {@code name}.
     *
     * <p>Every name the substitution rewrites was given an answer when it was put there — the
     * argument's own, or the binding this expansion made for it — so there is no name to be answered
     * with a guess. One missing is a substitution written without saying what it means.
     */
    private static ValueName substituted(Map<BindingId, ValueName> substDenotes, BindingId param) {
        ValueName denotes = substDenotes.get(param);
        if (denotes == null) {
            throw new IllegalStateException(param + " was substituted without an answer");
        }
        return denotes;
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
            collectHelperCalls(e.getValue().written(), called);
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
            collectValueNames(e.getValue().written(), out);
            edges.put(e.getKey(), out);
        }
        for (Map.Entry<String, Ast.FnDef> e : own.entrySet()) {
            if (!e.getValue().params().isEmpty()) {
                continue;   // a helper's own recursion is the call graph's business
            }
            // A value stands for a value. A block written as one — a `.field` getter, whose parameter
            // the compiler synthesizes — is refused where it is written rather than where it is used.
            //
            // Unless the definition says it is a function. Then the block is what that says it is,
            // and its parameters are the ones the written type names.
            boolean declaredAFunction = e.getValue().declaredReturn() != null
                    && e.getValue().declaredReturn().asFn() != null;
            if (!declaredAFunction && e.getValue().written() instanceof Ast.Block block) {
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
    private Ast.FnDef valueSpread(Ast.Var spread) {
        if (!(spread.denotes() instanceof ValueName.Helper)) {
            return null;
        }
        // by the name it is reached by here, which for another module's value is the qualified one
        String reached = spread.name();
        Ast.FnDef value = own.get(reached);
        return value == null || !value.params().isEmpty() || value.body() == null
                || recursive.contains(reached) ? null : value;
    }

    /** The names of this module's values that {@code e} reads. A value is written bare, so a
     * reference to one is a {@code Var} and never reaches the call graph. */
    private void collectValueNames(Ast.Expr e, Set<String> out) {
        if (e == null) {
            return;
        }
        if (e instanceof Ast.Var v && v.denotes() instanceof ValueName.Helper) {
            Ast.FnDef d = own.get(v.name());
            if (d != null && d.params().isEmpty()) {
                out.add(v.name());
            }
        }
        forEachChild(e, c -> collectValueNames(c, out));
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

    /**
     * Whether anything in {@code e} reads {@code binding}.
     *
     * <p>It asks what each name denotes, so a binder inside {@code e} that spells its name the same
     * is another binding and answers no. Nothing here tracks scope, because the tree already carries
     * the answer scope decided: that is what resolution is for.
     */
    private static boolean references(Ast.Expr e, BindingId binding) {
        ValueName denotes = switch (e) {
            case Ast.Var v -> v.denotes();
            case Ast.Apply c -> c.denotes();
            default -> null;
        };
        if (denotes instanceof ValueName.Local local && local.id().equals(binding)) {
            return true;
        }
        boolean[] found = {false};
        forEachChild(e, child -> found[0] |= references(child, binding));
        return found[0];
    }

    private void collectHelperCalls(Ast.Expr e, Set<String> out) {
        // Applying a function-typed parameter, or a binding holding a function, is not a call to
        // whatever else bears that name. The call carries what it resolved to, so it is asked rather
        // than matched against the helper table — a parameter named like a helper was reaching the
        // graph as a call to that helper, which made `let f (g: (Int) -> Int) = g(1)` recursive.
        if (e instanceof Ast.Apply call && !(call.denotes() instanceof ValueName.Local)) {
            // `List.fold` desugars to `List.foldFrom` before inlining, so a body that folds reaches the
            // recursive `foldFrom` — recursion classification and prelude-injection must see that.
            String fn = "List.fold".equals(call.reaches()) ? "List.foldFrom" : call.reaches();
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
