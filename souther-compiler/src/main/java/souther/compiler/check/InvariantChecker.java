package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.check.NumericDomain.LinearForm;
import souther.compiler.check.NumericDomain.Rel;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * The intraprocedural invariant-discharge check (spec §invariant-discharge). It walks a behavior's
 * body threading what the guards have settled — a {@link NumericDomain} of relations and a
 * {@link PredicateFacts} of everything that states no relation — seeded from the input types'
 * invariants and refined along each {@code guard}/{@code if} guard (a {@code guard} is already an
 * {@code if} here). At every construction whose invariant it can carry, it asks whether the guards
 * <em>discharge</em> it. A construction proven to violate its invariant on a reachable path is a
 * compile error (the path-sensitive generalization of the constant check {@code 金額(-5)}); one it
 * cannot prove is a warning (a possible abort — guard it, or reify the relation into a type
 * invariant). An invariant naming something it cannot name is left opaque (no diagnostic; the
 * run-time check stays), so every flagged construction has a guard that discharges it.
 *
 * <p>The walk mirrors {@link TotalityChecker}: a {@code switch} over {@code Ast.Expr} threading an
 * immutable environment. It is fail-open — any internal error is swallowed so an analysis bug can
 * never reject a valid program.
 */
public final class InvariantChecker {

    record Findings(List<CompileException> errors, List<Diagnostic> warnings) {}

    /**
     * What this check reads: one behavior's body and the invariants of the types around it, both in
     * the representation the rules are written at ({@link InliningPolicy#DISCHARGE}) rather than the
     * one the backend emits from.
     *
     * <p>{@code invariants} holds the declarations of the module being checked. A type another module
     * declares is absent, and its clause is read off the declaration in the settled form — where the
     * operations have already become the folds they are, so it falls outside the fragment.
     */
    public record Source(Ast.Expr body, Map<TypeName, List<Ast.InvariantClause>> invariants) {}

    /** A stdlib combinator whose closure (argument {@code closureArg}) is handed each element of its
     * container argument ({@code listArg}) as closure parameter {@code elementParam} — mirrors
     * {@link TotalityChecker}'s table, so a construction inside a {@code List.map} or
     * {@code List.foldFrom} closure is analyzed with the element bound to the container's element type
     * ({@link #elementType}).
     *
     * <p>A rule is keyed by the name a call still has when this tree is read, which is not every name
     * an author can write: {@code List.fold} is rewritten to {@code List.foldFrom} before any of this,
     * so a rule under that name could not be looked up. {@code InvariantCombinatorRulesTest} holds the
     * table to both halves of that — every name survives the rewrite, and every name has a program
     * that fires it. */
    private record Combinator(int closureArg, int elementParam, int listArg) {}

    private static final Map<String, Combinator> COMBINATORS = Map.ofEntries(
            Map.entry("List.foldFrom", new Combinator(0, 1, 2)),
            Map.entry("List.foldr", new Combinator(0, 1, 2)),
            Map.entry("List.map", new Combinator(0, 0, 1)),
            Map.entry("List.filter", new Combinator(0, 0, 1)),
            Map.entry("List.all", new Combinator(0, 0, 1)),
            Map.entry("List.any", new Combinator(0, 0, 1)),
            Map.entry("List.find", new Combinator(0, 0, 1)),
            Map.entry("List.partition", new Combinator(0, 0, 1)),
            Map.entry("List.concatMap", new Combinator(0, 0, 1)),
            Map.entry("List.filterMap", new Combinator(0, 0, 1)),
            Map.entry("List.sortBy", new Combinator(0, 0, 1)),
            Map.entry("List.groupBy", new Combinator(0, 0, 1)),
            Map.entry("List.indexBy", new Combinator(0, 0, 1)),
            Map.entry("List.allUniqueBy", new Combinator(0, 0, 1)),
            Map.entry("List.indexedMap", new Combinator(0, 1, 1)),
            Map.entry("Map.fold", new Combinator(0, 2, 2)),
            Map.entry("Map.map", new Combinator(0, 1, 1)),
            Map.entry("Map.filter", new Combinator(0, 1, 1)),
            Map.entry("Map.update", new Combinator(1, 0, 2)),
            Map.entry("Map.upsert", new Combinator(2, 0, 3)),
            Map.entry("Set.fold", new Combinator(0, 1, 2)),
            Map.entry("Set.map", new Combinator(0, 0, 1)),
            Map.entry("Set.filter", new Combinator(0, 0, 1)),
            Map.entry("Set.partition", new Combinator(0, 0, 1)),
            Map.entry("Option.map", new Combinator(0, 0, 1)));

    /** The operations the table has a rule for, for the test that holds it to being reachable. */
    static Set<String> combinatorNames() {
        return COMBINATORS.keySet();
    }

    /** The pure, total stdlib calls whose result is a number the domain can name: the size of a
     * container or a string. Each becomes an atom keyed by the call written over its argument's path
     * — {@code List.length(b.items)} — so an invariant clause and a guard naming the same container
     * name the same atom, and the guard discharges the clause. The argument must be a nameable path:
     * {@code List.length(List.map(f, xs))} is not this atom, and nothing relates the two. */
    private static final Set<String> SIZE_CALLS =
            Set.of("List.length", "String.length", "Set.size", "Map.size");

    /**
     * What a construction of a container keeps of the container it was built from. This is the table
     * that decides how much of a model the language tracks rather than leaves to a run-time check
     * (spec §invariant-discharge-preservation), and it is stated per operation because that is the
     * level an author writes at.
     *
     * <ul>
     * <li>{@code PERMUTES} — the same elements in another order. Everything survives.
     * <li>{@code SUBSET} — some of the same elements. Nothing new is there, so a property of every
     *     element survives and the size can only fall.
     * <li>{@code MAPS} — one new element for each. As many as before, and nothing is known of what
     *     they are.
     * <li>{@code COLLAPSES} — at most one new element for each. Neither the elements nor the count.
     * </ul>
     */
    private enum Shape {
        PERMUTES, SUBSET, MAPS, COLLAPSES;

        /** Whether the result has exactly as many as the container it was built from. */
        boolean keepsSize() {
            return this == PERMUTES || this == MAPS;
        }
    }

    /** Which argument a container was built from, and what the building keeps of it. */
    private record Built(int from, Shape shape) {}

    private static final Map<String, Built> BUILT_FROM = Map.ofEntries(
            Map.entry("List.reverse", new Built(0, Shape.PERMUTES)),
            Map.entry("List.sort", new Built(0, Shape.PERMUTES)),
            Map.entry("List.sortBy", new Built(1, Shape.PERMUTES)),
            Map.entry("List.map", new Built(1, Shape.MAPS)),
            Map.entry("List.indexedMap", new Built(1, Shape.MAPS)),
            Map.entry("Map.map", new Built(1, Shape.MAPS)),
            Map.entry("List.filter", new Built(1, Shape.SUBSET)),
            Map.entry("List.distinct", new Built(0, Shape.SUBSET)),
            Map.entry("List.take", new Built(1, Shape.SUBSET)),
            Map.entry("List.drop", new Built(1, Shape.SUBSET)),
            Map.entry("Set.filter", new Built(1, Shape.SUBSET)),
            Map.entry("Map.filter", new Built(1, Shape.SUBSET)),
            Map.entry("List.filterMap", new Built(1, Shape.COLLAPSES)),
            Map.entry("Set.map", new Built(1, Shape.COLLAPSES)));

    /** Where a predicate reads its container, and which shapes of construction carry it there.
     * {@code List.all} holds of any sublist of a list it holds of; {@code List.member} does not, and
     * neither survives a mapping — what a mapped element is, is #226's question. */
    private record Carried(int container, Set<Shape> through) {}

    /** Where a predicate reads the projection it is stated over. A mapping keeps a projection when
     * the closure copies that field from the element unchanged, so the predicate holds of the mapped
     * list exactly when it holds of what was mapped, over the field it came from. */
    private static final Map<String, Integer> PROJECTION_OF = Map.of("List.allUniqueBy", 0);

    private static final Map<String, Carried> CARRIED = Map.of(
            "List.all", new Carried(1, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            "List.allUniqueBy", new Carried(1, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            "List.any", new Carried(1, Set.of(Shape.PERMUTES)),
            "List.member", new Carried(1, Set.of(Shape.PERMUTES)),
            "Set.contains", new Carried(1, Set.of(Shape.PERMUTES)),
            "Map.containsKey", new Carried(1, Set.of(Shape.PERMUTES)));

    /** The calls that state their predicate of <em>every</em> element, so what they say of a
     * container is what holds of each element a closure is handed. Which argument is the predicate
     * and which the container is what {@link #COMBINATORS} already answers of any combinator, and how
     * far the statement travels is what {@link #CARRIED} already answers of any predicate — so a
     * quantifier is the name and nothing else. {@code List.all} is the only one the library has. */
    private static final Set<String> QUANTIFIERS = Set.of("List.all");

    /** Emptiness, by the size call it means. This is not a rule about what an operation does to a
     * property (spec §invariant-discharge-preservation) but about what a predicate <em>says</em>:
     * {@code List.isEmpty(xs)} and {@code List.length(xs) == 0} are one statement, so a guard writing
     * either discharges a clause writing the other. Without it the two would be unrelated, which is
     * an accident of which one the author reached for. */
    private static final Map<String, String> EMPTINESS = Map.of(
            "List.isEmpty", "List.length",
            "Set.isEmpty", "Set.size",
            "Map.isEmpty", "Map.size",
            "String.isEmpty", "String.length");

    private final Symbols symbols;
    private final Map<TypeName, List<Ast.InvariantClause>> dischargeInvariants;
    private final List<CompileException> errors = new ArrayList<>();
    private final List<Diagnostic> warnings = new ArrayList<>();

    private InvariantChecker(Symbols symbols,
                             Map<TypeName, List<Ast.InvariantClause>> dischargeInvariants) {
        this.symbols = symbols;
        this.dischargeInvariants = dischargeInvariants;
    }

    /** Every invariant that applies to {@code named}, each in the analysis representation where this
     * module declares it. */
    private List<Ast.InvariantClause> invariantsOf(TypeName named, Ast.Data data) {
        return TypeOps.effectiveInvariants(named, data, symbols, dischargeInvariants::get);
    }

    /**
     * A relation known of every element of a container. A fact settles the container as a whole and
     * is keyed by the call that states it, which relates it to nothing inside; this keeps the
     * relation as the clause it was written as, together with the rule that names its free leaves, so
     * it can be read again at the element a combinator's closure is handed.
     *
     * <p>{@code through} is how far it travels: a construction of one of those shapes holds only
     * elements of what it was built from, so what was stated of the source still holds of each of
     * them. {@code reads} is every term the <em>predicate</em> names from outside itself; a binding
     * that takes over one of those names leaves the predicate saying something else. The container is
     * kept apart from them because it is read where the call is written rather than inside the
     * closure, so a closure parameter spelling its root does not reach it.
     */
    private record Quantified(String container, Set<Shape> through, Ast.Block predicate,
                              Bindings binds, List<String> reads) {

        /** Whether a binding that drops what {@code drop} matches leaves the predicate intact. The
         * container is not asked: it is read outside the closure this is instantiated in. */
        boolean survives(java.util.function.Predicate<String> drop) {
            return reads.stream().noneMatch(drop);
        }
    }

    /** What the guards have settled on the current path: numeric relations, predicates known to hold
     * or to fail, and relations known of every element of a container. Threaded functionally through
     * the walk, as the domain alone once was. */
    private record Known(NumericDomain numbers, PredicateFacts facts, List<Quantified> quantified,
                         Set<String> spoken) {

        static Known top() {
            return new Known(NumericDomain.top(), PredicateFacts.none(), List.of(), Set.of());
        }

        Known with(NumericDomain n) {
            return new Known(n, facts, quantified, spoken);
        }

        Known with(PredicateFacts f) {
            return new Known(numbers, f, quantified, spoken);
        }

        /**
         * This, with each of {@code terms} recorded as one an assumption on this path named. It is
         * recorded where the assumption is made rather than searched for afterwards: what a guard
         * spoke about is known exactly then, and reading it back out of a domain would mean matching
         * key text, which is how a term that merely reads like another gets mistaken for it.
         */
        Known speaking(Collection<String> terms) {
            if (terms.isEmpty()) {
                return this;
            }
            Set<String> all = new HashSet<>(spoken);
            all.addAll(terms);
            return new Known(numbers, facts, quantified, Set.copyOf(all));
        }

        /** Whether an assumption on this path named {@code term}. */
        boolean speaksOf(String term) {
            return spoken.contains(term);
        }

        Known and(List<Quantified> more) {
            if (more.isEmpty()) {
                return this;
            }
            List<Quantified> all = new ArrayList<>(quantified);
            all.addAll(more);
            return new Known(numbers, facts, List.copyOf(all), spoken);
        }

        Known forgetIf(java.util.function.Predicate<String> drop) {
            List<Quantified> kept = new ArrayList<>();
            for (Quantified q : quantified) {
                // Here the container is asked too: a relation this walk carries past the binding is
                // one it may look up anywhere after it, where the name means what the binding gave.
                if (!drop.test(q.container()) && q.survives(drop)) {
                    kept.add(q);
                }
            }
            Set<String> said = new HashSet<>();
            for (String term : spoken) {
                if (!drop.test(term)) {
                    said.add(term);
                }
            }
            return new Known(numbers.forgetIf(drop), facts.forgetIf(drop), List.copyOf(kept),
                    Set.copyOf(said));
        }
    }

    /**
     * What the body's names mean where the walk is: the type of each, and, for a binding given a
     * location, the location it reads.
     *
     * <p>A binding given a location <em>is</em> that location — the rule {@link #pathKey} already
     * applies to a newtype's {@code .value}, read here of a name instead of a field. It is what lets
     * a construction survive being moved into a helper: an expansion binds each argument and answers
     * the parameter's reads with that binding (see {@link HelperInliner}), so without it the body of
     * a helper taking a record names locations the seeding never wrote, and everything an input's
     * type guarantees stops at the call.
     */
    private record Scope(Map<String, Type> types, Map<String, Denotes> denotations) {

        static Scope of(Map<String, Type> types) {
            return new Scope(types, Map.of());
        }

        Type typeOf(String name) {
            return types.get(name);
        }

        /** What {@code name} denotes, which is the location it is unless it was given something else. */
        Denotes denotes(String name) {
            return denotations.getOrDefault(name, new Denotes.Location(name));
        }

        /** The key {@code name} is known by, whichever kind of thing it denotes, or {@code null} where
         * it denotes nothing. */
        String keyOf(String name) {
            return denotes(name).key();
        }

        /**
         * This scope with {@code name} bound to {@code type} and to what it denotes. A binding whose
         * denotation was rooted at {@code name} loses it: the name it was written as denotes something
         * else from here, so what it stood for can no longer be said.
         */
        Scope binding(String name, Type type, Denotes what) {
            Map<String, Type> t = new HashMap<>(types);
            if (type == null) {
                t.remove(name);
            } else {
                t.put(name, type);
            }
            Map<String, Denotes> at = new HashMap<>(denotations);
            at.values().removeIf(d -> d.key() != null && mentions(d.key(), name));
            at.remove(name);
            if (!(what instanceof Denotes.Location loc && loc.key().equals(name))) {
                at.put(name, what);
            }
            return new Scope(Map.copyOf(t), Map.copyOf(at));
        }
    }

    /**
     * What a name denotes. The three are not one thing with a missing case: a location is somewhere the
     * seeding can have written about and a clause can have named, a term is a value known only by what
     * computes it, and nothing is nothing. Collapsing the last two would put a computed value where a
     * location is expected, which is the shape of {@code let} answering differently from the expression
     * it was given.
     */
    private sealed interface Denotes {

        /** The key this is known by, or {@code null} where it is known by none. */
        String key();

        /** A place: a parameter, a field chain, or another location a binding was given. */
        record Location(String key) implements Denotes {}

        /**
         * A value named by the expression that computes it. {@code byRule} is true where the check has
         * a rule about how it was built — a container the preservation table covers — and that rule is
         * what names it however it is reached; false where only a guard naming it can.
         */
        record Term(String key, boolean byRule) implements Denotes {}

        /** Nothing this check can name. */
        record Nothing() implements Denotes {

            @Override
            public String key() {
                return null;
            }
        }
    }

    /**
     * How a clause of {@code data}'s invariant can be discharged, read on its own — the construction
     * is assumed to name what it is given, so what is left is the clause's own shape. {@code at} is
     * where the clause is written, which is the pre-expansion position; {@code clause} is that clause
     * in the representation the check reads.
     */
    public static ClauseDischarge capabilityOf(Ast.Expr clause, SourcePos at, Ast.Data data,
                                               Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols, Map.of());
        Map<String, Type> fields = TypeOps.fieldTypes(data, symbols);
        Bindings binds = Bindings.ofPaths(
                name -> fields.containsKey(name) ? LinearForm.atom(name) : null,
                name -> fields.containsKey(name) ? name : null, fields);
        List<Clause> owed;
        try {
            owed = c.obligations(clause, binds);
        } catch (RuntimeException _) {
            owed = null;   // fail-open, as the walk is
        }
        if (owed == null || owed.isEmpty()) {
            return ClauseDischarge.runtimeOnly(at, c.whyUnreadable(clause, binds));
        }
        for (Clause owe : owed) {
            if (owe.numeric() != null) {
                return ClauseDischarge.derivable(at);
            }
        }
        return ClauseDischarge.exactMatch(at);
    }

    /** What in {@code clause} the check cannot read, said so an author can act on it. */
    private String whyUnreadable(Ast.Expr clause, Bindings binds) {
        Ast.Expr blocked = unreadable(clause);
        if (blocked instanceof Ast.Apply call) {
            return "it calls `" + call.written() + "`, which the check reads as a value and not as a term";
        }
        if (blocked != null) {
            return "it is not one of the shapes the check reads";
        }
        String name = unnamed(clause, binds, Set.of());
        if (name != null) {
            return "it reads `" + name + "`, and a clause is read through the fields the construction"
                    + " fills";
        }
        return "it names a term the check cannot name";
    }

    /** A name the clause reads that is neither a field of the declaration nor bound inside the clause,
     * or {@code null} if it reads none. */
    private String unnamed(Ast.Expr e, Bindings binds, Set<String> bound) {
        if (e instanceof Ast.Var v) {
            return bound.contains(v.name()) || binds.path().apply(v.name()) != null ? null : v.name();
        }
        Set<String> inner = bound;
        if (e instanceof Ast.Block b && !b.params().isEmpty()) {
            inner = new java.util.HashSet<>(bound);
            inner.addAll(b.paramNames());
        } else if (e instanceof Ast.LetIn li) {
            inner = new java.util.HashSet<>(bound);
            inner.add(li.name());
        }
        Set<String> scope = inner;
        String[] found = {null};
        Ast.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = unnamed(child, binds, scope);
            }
        });
        return found[0];
    }

    /** The innermost part of {@code e} the term grammar cannot read, or {@code null} if it reads all
     * of it. Every location is granted, so what is left is the shape. */
    private Ast.Expr unreadable(Ast.Expr e) {
        Ast.Expr[] found = {null};
        Ast.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = unreadable(child);
            }
        });
        if (found[0] != null) {
            return found[0];
        }
        return termKey(e, x -> rootName(x) != null ? "?" : null, Map.of(), 0) == null ? e : null;
    }

    /** Analyzes one behavior body against its input scope. Never throws. A {@code null} source is a
     * body the analysis representation could not be built for, and is not analyzed at all. */
    static Findings analyze(Source source, Map<String, Type> params, Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols, source == null ? Map.of() : source.invariants());
        if (source == null) {
            return new Findings(c.errors, c.warnings);
        }
        try {
            Known k = Known.top();
            for (Map.Entry<String, Type> p : params.entrySet()) {
                k = c.seedParam(p.getKey(), p.getValue(), k);
            }
            c.walk(source.body(), k, Scope.of(params));
        } catch (RuntimeException _) {
            // fail-open: the run-time invariant check remains the backstop
        }
        return new Findings(c.errors, c.warnings);
    }

    // --- the walk ------------------------------------------------------------------------------

    private void walk(Ast.Expr e, Known k, Scope scope) {
        checkIfConstruction(e, k, scope, false);
        switch (e) {
            case Ast.If iff -> {
                walk(iff.cond(), k, scope);
                walk(iff.then(), assumeCond(iff.cond(), k, scope, true), scope);
                walk(iff.els(), assumeCond(iff.cond(), k, scope, false), scope);
            }
            case Ast.IfConstructed ic -> {
                // The attempt's own construction cannot abort — a failing invariant is the else
                // branch — so it is checked for a decided violation and never warned about as a
                // possible one. Its field values are walked on their own so a construction nested
                // inside an argument is still an ordinary, aborting one.
                checkIfConstruction(ic.construct(), k, scope, true);
                Ast.forEachChild(ic.construct(), child -> walk(child, k, scope));
                Known k2 = rebind(k, ic.binderName());
                Type built = typeExpr(ic.construct(), scope);
                // The attempt built the value, so the binding is that construction and no location
                if (built != null) {
                    k2 = seedParam(ic.binderName(), built, k2);   // on this branch the invariant holds
                }
                walk(ic.then(), k2, scope.binding(ic.binderName(), built,
                        new Denotes.Location(ic.binderName())));
                // Each departure stands where the invariant did not hold, and nothing was built
                // there, so none of them is seeded with anything the attempt would have guaranteed.
                ic.els().forEach(arm -> walk(arm.body(), k, scope));
            }
            case Ast.LetIn li -> {
                walk(li.value(), k, scope);
                Type vt = typeExpr(li.value(), scope);
                // The name is an alias for what its initializer denotes, so what is recorded about it
                // is recorded under that denotation and not under the spelling. Recording it under the
                // name is what made a named subexpression a term of its own, answering differently
                // from the very expression it was given.
                Denotes what = denotationOf(li.value(), scope);
                LinearForm vf = affineOf(li.value(), scope);
                Known k2 = rebind(k, li.name());
                if (isNumeric(vt) && vf != null && what.key() != null) {
                    k2 = k2.with(k2.numbers().assign(what.key(), vf));
                }
                walk(li.body(), k2, scope.binding(li.name(), vt, what));
            }
            case Ast.Match m -> {
                walk(m.scrutinee(), k, scope);
                for (Ast.Case c : m.cases()) {
                    Scope s2 = scope;
                    Known k2 = k;
                    if (c.binding() != null) {
                        k2 = rebind(k, c.bindingName());
                        Type bound = c.caseTypes().size() == 1
                                ? MatchElaborator.caseBindType(c.caseTypes().get(0).denotes()) : null;
                        // A sum has no fields of its own, so the scrutinee is not a location any
                        // clause could have named — the case's value names only itself.
                        s2 = scope.binding(c.bindingName(), bound, new Denotes.Location(c.bindingName()));
                    }
                    walk(c.body(), k2, s2);
                }
            }
            case Ast.Apply call -> walkCall(call, k, scope);
            default -> Ast.forEachChild(e, child -> walk(child, k, scope));
        }
    }

    /** Walks a call, binding a combinator closure's element parameter to the list's element type (and
     * seeding its invariant) so a construction inside the closure is analyzed rather than left opaque. */
    private void walkCall(Ast.Apply call, Known k, Scope scope) {
        Combinator combo = COMBINATORS.get(call.reaches());
        for (int i = 0; i < call.args().size(); i++) {
            Ast.Expr arg = call.args().get(i);
            if (combo != null && i == combo.closureArg() && arg instanceof Ast.Block step
                    && combo.elementParam() < step.params().size()
                    && combo.listArg() < call.args().size()) {
                Ast.Expr container = call.args().get(combo.listArg());
                Type elem = elementType(typeExpr(container, scope));
                // The container is read where the call is written, so what is known of its elements
                // is looked up before the closure's parameter takes any name over. Reading it after
                // would make an argument spelling that name — `List.map(cart -> ..., cart.items)` —
                // answer differently from one spelling any other, which is nothing the program says.
                List<Quantified> relations = elementRelations(container, k, scope);
                String p = step.params().get(combo.elementParam()).name();
                // an element of a container is not a location the body can otherwise name
                Scope s2 = scope.binding(p, elem, new Denotes.Location(p));
                Known k2 = rebind(k, p);
                if (elem != null) {
                    k2 = seedParam(p, elem, k2);   // the element carries its type's invariant
                }
                for (Quantified q : relations) {
                    // What the predicate reads besides the element is still read inside the closure,
                    // so a parameter that takes one of those names over does leave it saying
                    // something else.
                    if (q.survives(key -> mentions(key, p))) {
                        k2 = instantiate(q, p, elem, k2);
                    }
                }
                walk(step.body(), k2, s2);
            } else {
                walk(arg, k, scope);
            }
        }
    }

    /** The relations known of every element of {@code container}: those stated of it as written, and
     * those stated of a container it was built from that travel every construction in between. */
    private List<Quantified> elementRelations(Ast.Expr container, Known k, Scope scope) {
        List<Quantified> found = new ArrayList<>();
        Set<Shape> crossed = java.util.EnumSet.noneOf(Shape.class);
        Ast.Expr source = container;
        while (true) {
            String key = bodyKey(source, scope);
            if (key != null) {
                for (Quantified q : k.quantified()) {
                    if (key.equals(q.container()) && q.through().containsAll(crossed)) {
                        found.add(q);
                    }
                }
            }
            if (!(source instanceof Ast.Apply call)) {
                return found;
            }
            Built built = BUILT_FROM.get(call.reaches());
            if (built == null || built.from() >= call.args().size()) {
                return found;
            }
            crossed.add(built.shape());
            source = call.args().get(built.from());
        }
    }

    /** What {@code q} says of the element bound to {@code element}, taken into {@code k}. The clause
     * is read again with the quantifier's own parameter standing for that element — the same reading
     * {@link #seedAt} does of a type's invariant, over the clause a quantifier holds. A relation the
     * clause in turn states of a container is recorded, so a container of containers reaches its
     * innermost element. */
    private Known instantiate(Quantified q, String element, Type elementType, Known k) {
        Ast.Binder param = q.predicate().params().get(0);
        Map<String, Type> fields = new HashMap<>(q.binds().fields());
        if (elementType != null) {
            fields.put(param.name(), elementType);
        }
        Bindings at = new Bindings(
                name -> param.name().equals(name)
                        ? LinearForm.atom(element) : q.binds().form().apply(name),
                name -> param.name().equals(name) ? element : q.binds().path().apply(name),
                q.binds().given(), q.binds().bodyKey(), fields);
        List<Quantified> nested = new ArrayList<>();
        quantifiedBy(q.predicate().body(), at, true, nested);
        return assume(obligations(q.predicate().body(), at), k).and(nested);
    }

    /** What {@code e}, asserted with polarity {@code positive}, says of every element of a container.
     * Mirrors {@link #obligations}: a conjunction states each of its sides, and a negation flips the
     * polarity. Only a stated quantifier is recorded — denying one says some element fails the
     * predicate, and which one is not something this check can name. */
    private void quantifiedBy(Ast.Expr raw, Bindings binds, boolean positive, List<Quantified> out) {
        Ast.Expr e = asSizeComparison(raw);
        if (e instanceof Ast.Binary b && b.op() == Ast.BinOp.AND && positive) {
            quantifiedBy(b.left(), binds, true, out);
            quantifiedBy(b.right(), binds, true, out);
            return;
        }
        Ast.Expr under = negated(e);
        if (under != null) {
            quantifiedBy(under, binds, !positive, out);
            return;
        }
        if (!positive || !(e instanceof Ast.Apply call) || !QUANTIFIERS.contains(call.reaches())) {
            return;
        }
        Combinator over = COMBINATORS.get(call.reaches());
        Carried carried = CARRIED.get(call.reaches());
        if (over == null || carried == null || over.closureArg() >= call.args().size()
                || over.listArg() >= call.args().size()
                || !(call.args().get(over.closureArg()) instanceof Ast.Block p)
                || p.params().size() != 1) {
            return;
        }
        String container = siteOf(binds).apply(call.args().get(over.listArg()));
        if (container == null) {
            return;
        }
        List<String> named = new ArrayList<>();
        reads(p, binds, Set.of(), named);   // the predicate's own parameter is its own, and left out
        out.add(new Quantified(container, carried.through(), p, binds, List.copyOf(named)));
    }

    /** Every term {@code e} names from outside itself, as the clause's own rule names it. A name the
     * clause binds is its own and is left out; anything else the rule cannot name is kept as written,
     * which can only drop the relation sooner. */
    private void reads(Ast.Expr e, Bindings binds, Set<String> bound, List<String> out) {
        String root = rootName(e);
        if (root != null) {
            if (!bound.contains(root)) {
                String path = invPath(e, binds);
                out.add(path == null ? root : path);
            }
            return;
        }
        Set<String> inner = bound;
        if (e instanceof Ast.Block b && !b.params().isEmpty()) {
            inner = new java.util.HashSet<>(bound);
            inner.addAll(b.paramNames());
        } else if (e instanceof Ast.LetIn li) {
            inner = new java.util.HashSet<>(bound);
            inner.add(li.name());
        }
        Set<String> scope = inner;
        Ast.forEachChild(e, child -> reads(child, binds, scope, out));
    }

    // --- construction detection & discharge check ----------------------------------------------

    private void checkIfConstruction(Ast.Expr e, Known k, Scope scope,
                                     boolean attempted) {
        switch (e) {
            case Ast.NewData nd when nd.spreads().isEmpty() -> {
                if (symbols.get(nd.typeName().denotes()) instanceof Ast.Data type) {
                    Map<String, LinearForm> forms = new HashMap<>();
                    Map<String, String> paths = new HashMap<>();
                    Map<String, Ast.Expr> given = new HashMap<>();
                    Function<Ast.Expr, String> bodyKey = value -> siteKey(value, scope, k);
                    for (Ast.FieldInit fi : nd.inits()) {
                        LinearForm f = affineOf(fi.value(), scope);
                        if (f != null) {
                            forms.put(fi.name(), f);
                        }
                        String p = bodyKey.apply(fi.value());
                        if (p != null) {
                            paths.put(fi.name(), p);
                        }
                        given.put(fi.name(), fi.value());
                    }
                    check(nd.typeName().denotes(), type,
                            new Bindings(forms::get, paths::get, given::get, bodyKey,
                                    TypeOps.fieldTypes(type, symbols)),
                            k, nd.pos(), attempted);
                }
            }
            case Ast.Binary bin when isArith(bin.op()) -> {
                if (typeExpr(bin, scope) instanceof Type.Ref r
                        && symbols.get(r.name()) instanceof Ast.Data type && type.newtype()) {
                    LinearForm value = affineOf(bin, scope);
                    if (value != null) {
                        // an arithmetic result is a form, not a location, so it names no path
                        check(r.name(), type,
                                Bindings.ofPaths(name -> "value".equals(name) ? value : null, _ -> null,
                                        TypeOps.fieldTypes(type, symbols)),
                                k, bin.pos(), attempted);
                    }
                }
            }
            default -> { }
        }
    }

    /** How an invariant's leaf names resolve at a construction site: to the affine form of what the
     * field is being given, and to that value's canonical path — so a size call over the field names
     * the same atom the body names when it calls the same function on the same container. */
    private record Bindings(Function<String, LinearForm> form, Function<String, String> path,
                            Function<String, Ast.Expr> given, Function<Ast.Expr, String> bodyKey,
                            Map<String, Type> fields) {

        /** A clause naming only fields, with nothing of the site to look through — what seeding has. */
        static Bindings ofPaths(Function<String, LinearForm> form, Function<String, String> path,
                                Map<String, Type> fields) {
            return new Bindings(form, path, _ -> null, _ -> null, fields);
        }

        /** Nothing to substitute: what the body's own expressions are read with. */
        static Bindings ofBody(Function<Ast.Expr, String> bodyKey) {
            return new Bindings(_ -> null, _ -> null, _ -> null, bodyKey, Map.of());
        }

        /** A clause written in the body's own scope, where every name already stands for itself —
         * what a guard states, read by the rule a type's clause is read by. */
        static Bindings ofScope(Scope scope) {
            return ofPaths(name -> scope.keyOf(name) == null ? null : LinearForm.atom(scope.keyOf(name)),
                    scope::keyOf,
                    scope.types());
        }
    }

    /** How a clause's own expression is named: through the fields the construction is filling, and
     * through nothing else. A body expression reaches the same space of keys only by being
     * substituted for a field, which is what {@link #resolve} does. */
    private Function<Ast.Expr, String> siteOf(Bindings binds) {
        return e -> termKey(e, x -> invPath(x, binds), Map.of(), 0);
    }

    /** The expression a clause's leaf stands for at the construction site, or {@code null} when the
     * clause names something the site does not hand over. A rule about how a container was built has
     * to read the construction's own expression: the clause writes {@code value}, and what
     * {@code value} is being given is where the operations are. */
    private static Ast.Expr atSite(Ast.Expr e, Bindings binds) {
        return e instanceof Ast.Var v ? binds.given().apply(v.name()) : null;
    }

    /** Runs the discharge check for a construction of {@code type} whose field values resolve through
     * {@code binds}. A definite violation is an error; an unproven one a warning; a fully-discharged
     * or non-expressible invariant is silent. An {@code attempted} construction raises no warning:
     * what the warning reports is a possible abort, and an attempt takes its else branch instead. */
    private void check(TypeName named, Ast.Data type, Bindings binds, Known k, SourcePos pos,
                       boolean attempted) {
        List<Ast.InvariantClause> invs = invariantsOf(named, type);
        if (invs.isEmpty()) {
            return;
        }
        List<Clause> owed = new ArrayList<>();
        for (Ast.InvariantClause inv : invs) {
            List<Clause> o = obligations(inv.expr(), binds);
            if (o != null) {
                owed.addAll(o);
            }
        }
        if (owed.isEmpty()) {
            return;   // nothing here is expressible — the run-time check stands for all of it
        }
        NumericDomain dom = k.numbers();
        for (Clause c : owed) {
            for (Constraint known : c.known()) {
                dom = dom.assume(known.form(), known.rel());
            }
        }
        boolean possible = false;
        for (Clause c : owed) {
            if (c.dischargedBy(dom, k.facts())) {
                continue;
            }
            if (c.refutedBy(dom, k.facts())) {
                reportViolation(type, pos);
                return;
            }
            possible = true;
        }
        if (possible && !attempted) {
            warnings.add(
                    Diagnostic.of("E2011", "check.invariant.unproven").title("check.invariant.title")
                            .at(pos).args(type.name()).hint("check.invariant.reify", type.name())
                            .warning().build());
        }
    }

    private void reportViolation(Ast.Data type, SourcePos pos) {
        errors.add(CompileException.of(
                Diagnostic.of("E2010", "check.invariant.violation").title("check.invariant.title")
                        .at(pos).args(type.name()).build(),
                "constructing `" + type.name() + "` here violates its invariant on a reachable path"));
    }

    // --- invariant / condition -> constraints --------------------------------------------------

    private record Constraint(LinearForm form, Rel rel) {}

    /**
     * A predicate stated of a term. {@code keys} is the term as written first, then each container it
     * was built from by a construction that carries the predicate — any one of them settled is this
     * clause established. Refuting reads only the first: denying a predicate of a list says nothing
     * about a list built from it. {@code positive} is false for a clause written under a negation,
     * and such a clause carries nowhere, since the implication runs the other way.
     */
    private record Fact(List<String> keys, boolean positive) {

        boolean entailedBy(PredicateFacts facts) {
            for (String key : keys) {
                if (facts.entails(key, positive)) {
                    return true;
                }
            }
            return false;
        }

        boolean refutedBy(PredicateFacts facts) {
            return facts.refutes(keys.get(0), positive);
        }
    }

    /**
     * One clause of an invariant, and the two ways it can come out: a relation for the domain to
     * prove, and the key a guard restating it settles. Either may be absent, and where both are
     * present either one discharging the clause is enough — a guard is written one way and a clause
     * another, and which of the two routes carries it is not the author's concern.
     */
    private record Clause(Constraint numeric, Fact fact, List<Constraint> known) {

        boolean dischargedBy(NumericDomain d, PredicateFacts facts) {
            return numeric != null && d.entails(numeric.form(), numeric.rel())
                    || fact != null && fact.entailedBy(facts);
        }

        boolean refutedBy(NumericDomain d, PredicateFacts facts) {
            return numeric != null && d.refutes(numeric.form(), numeric.rel())
                    || fact != null && fact.refutedBy(facts);
        }
    }

    /** What an invariant expression owes under {@code binds} (field/{@code value} name -> what it is
     * being given), or {@code null} if it names nothing this check can carry. A comparison the domain
     * can express is owed to the domain; anything else is owed as a fact, which a guard stating the
     * same thing of the same term settles. */
    private List<Clause> obligations(Ast.Expr inv, Bindings binds) {
        return obligations(inv, binds, true);
    }

    private List<Clause> obligations(Ast.Expr rawInv, Bindings binds, boolean positive) {
        Ast.Expr inv = asSizeComparison(rawInv);
        if (inv instanceof Ast.Binary b && b.op() == Ast.BinOp.AND && positive) {
            // Each conjunct on its own: an invariant is a set of things that hold, and one the check
            // cannot read leaves its own run-time check standing without costing the others theirs.
            List<Clause> l = obligations(b.left(), binds, true);
            List<Clause> r = obligations(b.right(), binds, true);
            if (l == null && r == null) {
                return null;
            }
            List<Clause> both = new ArrayList<>(l == null ? List.of() : l);
            both.addAll(r == null ? List.of() : r);
            return both;
        }
        Ast.Expr under = negated(inv);
        if (under != null) {
            return obligations(under, binds, !positive);
        }
        Boolean folded = decidedAt(inv, binds);
        if (folded != null && folded == positive) {
            // The clause folds once the construction's own expressions stand where it wrote a field,
            // and it folds the way it is being read. There is nothing to owe. Read under a negation
            // it is the other answer that discharges, which is why the polarity is asked: folding to
            // true under a denial is a violation and not a discharge.
            return List.of();
        }
        Constraint numeric = null;
        if (inv instanceof Ast.Binary b && relOf(b.op()) != null) {
            Rel eff = positive ? relOf(b.op()) : negateRel(relOf(b.op()));
            LinearForm la = eff == null ? null : affine(b.left(), resolveLeaf(binds));
            LinearForm ra = eff == null ? null : affine(b.right(), resolveLeaf(binds));
            if (la != null && ra != null) {
                numeric = new Constraint(la.minus(ra), eff);
            }
        }
        Polar polar = polar(inv, positive);
        List<String> keys = factKeys(polar.expr(), binds);
        boolean stated = polar.positive();
        Fact fact = keys.isEmpty() ? null : new Fact(stated ? keys : firstOnly(keys), stated);
        if (numeric == null && fact == null) {
            return null;
        }
        List<Constraint> known = new ArrayList<>();
        sizeFacts(inv, binds, known);
        return List.of(new Clause(numeric, fact, known));
    }

    /** Whether {@code inv} is decided outright at this construction: the clause with each field it
     * names replaced by what the construction gives that field, folded. {@code null} where it does not
     * fold — which is every clause reading anything computed at run time. */
    private Boolean decidedAt(Ast.Expr inv, Bindings binds) {
        Object folded = ConstEval.eval(substituted(inv, binds)).orElse(null);
        return folded instanceof Boolean b ? b : null;
    }

    /** {@code inv} with every name the construction fills replaced by the expression filling it. */
    private static Ast.Expr substituted(Ast.Expr e, Bindings binds) {
        Ast.Expr given = atSite(e, binds);
        if (given != null) {
            return given;
        }
        return Ast.mapChildren(e, child -> substituted(child, binds), name -> name);
    }

    private static List<String> firstOnly(List<String> keys) {
        return keys.isEmpty() ? keys : List.of(keys.get(0));
    }

    /** Refines {@code k} by asserting {@code cond} (or its negation): a comparison tightens the
     * numeric domain, a stdlib predicate settles a fact. A condition of neither shape, and an operand
     * outside the affine fragment, leave {@code k} unchanged (sound). */
    private Known assumeCond(Ast.Expr rawCond, Known k, Scope scope, boolean positive) {
        Ast.Expr cond = asSizeComparison(rawCond);
        // `&&` asserted true gives both sides; `||` asserted false gives both sides negated.
        if (cond instanceof Ast.Binary b
                && (b.op() == Ast.BinOp.AND && positive || b.op() == Ast.BinOp.OR && !positive)) {
            return assumeCond(b.right(), assumeCond(b.left(), k, scope, positive), scope, positive);
        }
        Ast.Expr under = negated(cond);
        if (under != null) {
            return assumeCond(under, k, scope, !positive);
        }
        Known out = k;
        // What holds of the sizes the condition names, whichever way the condition itself is read.
        List<Constraint> known = new ArrayList<>();
        sizeFacts(cond, scope, known);
        for (Constraint c : known) {
            out = out.with(out.numbers().assume(c.form(), c.rel()));
        }
        if (cond instanceof Ast.Binary b) {
            Rel rel = relOf(b.op());
            Rel eff = rel == null ? null : positive ? rel : negateRel(rel);
            LinearForm la = eff == null ? null : affineOf(b.left(), scope);
            LinearForm ra = eff == null ? null : affineOf(b.right(), scope);
            if (la != null && ra != null) {
                out = out.with(out.numbers().assume(la.minus(ra), eff));
            }
            // What the comparison named, recorded as spoken about: a construction from one of these
            // is one the author has said something about, whichever route ends up carrying it.
            out = out.speaking(spokenOf(b.left(), scope, la));
            out = out.speaking(spokenOf(b.right(), scope, ra));
        }
        List<Quantified> quantified = new ArrayList<>();
        quantifiedBy(cond, Bindings.ofScope(scope), positive, quantified);
        out = out.and(quantified);
        // Both routes, always: which one carries a clause is decided where the clause is read, and a
        // guard does not know which that will be.
        Polar polar = polar(cond, positive);
        String key = bodyKey(polar.expr(), scope);
        return key == null ? out : out.with(out.facts().assume(key, polar.positive()));
    }

    /** The terms one side of a compared pair names: the expression itself, and each atom of the form it
     * reduced to — {@code leftover + 1} says something about {@code leftover}. */
    private Collection<String> spokenOf(Ast.Expr side, Scope scope, LinearForm form) {
        Set<String> terms = new HashSet<>(form == null ? Set.of() : form.coefs().keySet());
        String written = bodyKey(side, scope);
        if (written != null) {
            terms.add(written);
        }
        return terms;
    }

    /** A predicate as one of {@code ==}/{@code <} states it, and whether it is being stated or denied. */
    private record Polar(Ast.Expr expr, boolean positive) {}

    /**
     * {@code e}, asserted with polarity {@code positive}, as the comparison of {@code ==} or {@code <}
     * that says the same thing: {@code a /= b} is {@code a == b} denied, {@code a >= b} is
     * {@code a < b} denied, and {@code a > b} is {@code b < a}. A fact is settled by key equality, so
     * without this the six ways to compare two terms are six facts, and a guard written one way would
     * leave a clause written the other unsettled.
     */
    private static Polar polar(Ast.Expr e, boolean positive) {
        if (!(e instanceof Ast.Binary b) || relOf(b.op()) == null) {
            return new Polar(e, positive);
        }
        return switch (b.op()) {
            case NE -> new Polar(comparison(Ast.BinOp.EQ, b.left(), b.right(), b), !positive);
            case GE -> new Polar(comparison(Ast.BinOp.LT, b.left(), b.right(), b), !positive);
            case GT -> new Polar(comparison(Ast.BinOp.LT, b.right(), b.left(), b), positive);
            case LE -> new Polar(comparison(Ast.BinOp.LT, b.right(), b.left(), b), !positive);
            default -> new Polar(e, positive);
        };
    }

    private static Ast.Binary comparison(Ast.BinOp op, Ast.Expr left, Ast.Expr right, Ast.Binary of) {
        return new Ast.Binary(op, left, right, of.pos());
    }

    /** What a negation is applied to, or {@code null} if {@code e} is not one. {@code Bool.not} is an
     * ordinary helper: the analysis representation keeps it as a call, and a clause read off an
     * imported declaration is the body it expands to — {@code if b then false else true} over a
     * binding holding the argument. Both are read. */
    private static Ast.Expr negated(Ast.Expr e) {
        if (e instanceof Ast.Apply call && "Bool.not".equals(call.reaches()) && call.args().size() == 1) {
            return call.args().get(0);
        }
        if (e instanceof Ast.LetIn li) {
            Ast.Expr inner = negated(li.body());
            return inner instanceof Ast.Var v && v.name().equals(li.name()) ? li.value() : null;
        }
        return e instanceof Ast.If iff
                && iff.then() instanceof Ast.BoolLit t && !t.value()
                && iff.els() instanceof Ast.BoolLit f && f.value()
                ? iff.cond() : null;
    }

    // --- seeding -------------------------------------------------------------------------------

    /** Seeds the check with what a parameter's type guarantees: a numeric newtype's own invariant on
     * its value, a predicate its invariant states of it, or a product data's invariant over its fields
     * (and one level of fields), each substituted onto the parameter's own term. Sound by closed
     * construction — an input of type T was built through T's checked constructor. */
    private Known seedParam(String name, Type t, Known k) {
        return seedAt(name, t, k, 0);
    }

    /** {@code k} with everything {@code owed} states taken as holding. What a clause owes at a
     * construction is what it guarantees where it is already established, so the two read the same
     * clauses through the same rule and differ only in direction. */
    private Known assume(List<Clause> owed, Known k) {
        if (owed == null) {
            return k;
        }
        Known out = k;
        for (Clause c : owed) {
            for (Constraint known : c.known()) {
                out = out.with(out.numbers().assume(known.form(), known.rel()));
            }
            if (c.numeric() != null) {
                out = out.with(out.numbers().assume(c.numeric().form(), c.numeric().rel()));
            }
            if (c.fact() != null) {
                // What is guaranteed is guaranteed of the term as written; a container built from it
                // is another term, and reads the rules where it is constructed rather than here.
                out = out.with(out.facts().assume(c.fact().keys().get(0), c.fact().positive()));
            }
        }
        return out;
    }

    private Known seedAt(String path, Type t, Known k, int depth) {
        if (depth > 2 || !(t instanceof Type.Ref ref) || !(symbols.get(ref.name()) instanceof Ast.Data data)) {
            return k;
        }
        Map<String, Type> fields = TypeOps.fieldTypes(data, symbols);
        Function<String, String> resolvePath = fieldName -> {
            if (data.newtype() && fieldName.equals("value")) {
                return path;
            }
            return fields.containsKey(fieldName) ? path + "." + fieldName : null;
        };
        Bindings binds = Bindings.ofPaths(
                fieldName -> {
                    String p = resolvePath.apply(fieldName);
                    return p == null ? null : LinearForm.atom(p);
                },
                resolvePath, fields);
        Known out = k;
        List<Quantified> quantified = new ArrayList<>();
        for (Ast.InvariantClause inv : invariantsOf(ref.name(), data)) {
            quantifiedBy(inv.expr(), binds, true, quantified);
            out = assume(obligations(inv.expr(), binds), out);
        }
        out = out.and(quantified);
        if (data.newtype()) {
            // A newtype's `.value` is the same location as the newtype, so what its base guarantees is
            // guaranteed of this very atom: `data Outer = Inner` carries Inner's invariant.
            out = seedAt(path, fields.get("value"), out, depth + 1);
        } else {
            for (Map.Entry<String, Type> f : fields.entrySet()) {
                out = seedAt(path + "." + f.getKey(), f.getValue(), out, depth + 1);
            }
        }
        return out;
    }

    // --- affine forms --------------------------------------------------------------------------

    /**
     * The library's function forms of the arithmetic operators, and the operator each one is. They
     * reach the same kernel in the same argument order — {@code Int.add} is {@code IntMath.addExact},
     * which is what {@code +} emits — so the two spellings compute one value and are read as one term.
     * {@code divide} is absent: it answers a union rather than a number.
     */
    private static final Map<String, Ast.BinOp> OPERATOR_CALLS = Map.of(
            "Int.add", Ast.BinOp.ADD,
            "Int.subtract", Ast.BinOp.SUB,
            "Int.multiply", Ast.BinOp.MUL,
            "Decimal.add", Ast.BinOp.ADD,
            "Decimal.subtract", Ast.BinOp.SUB,
            "Decimal.multiply", Ast.BinOp.MUL);

    /** The operator {@code e} is, where it is a library call written as a function, or {@code e}
     * itself. Reading it as the operator is what puts it on the one path the operator already has,
     * rather than on a second path that would have to be kept saying the same thing. */
    private static Ast.Expr asOperator(Ast.Expr e) {
        if (e instanceof Ast.Apply call && call.args().size() == 2) {
            Ast.BinOp op = OPERATOR_CALLS.get(call.reaches());
            if (op != null) {
                return new Ast.Binary(op, call.args().get(0), call.args().get(1), call.pos());
            }
        }
        return e;
    }

    /** The shared affine walk: literals and {@code +}/{@code -} compose; every other node is handed to
     * {@code leaf} (which decides whether it is an atom, a resolved field, or opaque). */
    private LinearForm affine(Ast.Expr raw, Function<Ast.Expr, LinearForm> leaf) {
        Ast.Expr e = asOperator(raw);
        return switch (e) {
            // A call that folds is the number it folds to. `String.length("1A")` is 2, and a clause
            // about it is decided rather than owed — the run-time check is not what should answer a
            // question the compiler has already computed.
            case Ast.Apply call when constantNumber(call) != null ->
                    LinearForm.constant(constantNumber(call));
            case Ast.IntLit i -> LinearForm.constant(BigDecimal.valueOf(i.value()));
            case Ast.DecimalLit dd -> LinearForm.constant(dd.value());
            case Ast.Neg n -> negate(affine(n.operand(), leaf));
            case Ast.Binary b when b.op() == Ast.BinOp.ADD ->
                    add(affine(b.left(), leaf), affine(b.right(), leaf), false);
            case Ast.Binary b when b.op() == Ast.BinOp.SUB ->
                    add(affine(b.left(), leaf), affine(b.right(), leaf), true);
            // scalar multiply by a constant (金額 * 2) is linear; `/` and a variable product are not
            // (a divide truncates for Int, and a variable factor is non-linear), so leave those opaque.
            case Ast.Binary b when b.op() == Ast.BinOp.MUL ->
                    scale(affine(b.left(), leaf), affine(b.right(), leaf));
            // A binding an expansion introduced ({@code let $0_n = n.value in $0_n * 2}) is what an
            // arithmetic helper becomes, so reading through it is reading the arithmetic the author
            // wrote. An inner binding of the same name makes its own rule first, which is what
            // shadowing is.
            case Ast.LetIn li -> {
                LinearForm bound = affine(li.value(), leaf);
                yield bound == null ? leaf.apply(e) : affine(li.body(),
                        n -> n instanceof Ast.Var v && v.name().equals(li.name())
                                ? bound : leaf.apply(n));
            }
            default -> leaf.apply(e);
        };
    }

    /** The number {@code e} folds to at compile time, or {@code null} where it folds to none. */
    private static BigDecimal constantNumber(Ast.Expr e) {
        Object folded = ConstEval.eval(e).orElse(null);
        if (folded instanceof Long n) {
            return BigDecimal.valueOf(n);
        }
        return folded instanceof BigDecimal d ? d : null;
    }

    /** A linear form scaled by a constant, when one side is a bare constant (a scalar multiply); null
     * when neither side is constant (a non-linear product). */
    private static LinearForm scale(LinearForm a, LinearForm b) {
        if (a == null || b == null) {
            return null;
        }
        if (a.coefs().isEmpty()) {
            return b.times(a.constant());
        }
        return b.coefs().isEmpty() ? a.times(b.constant()) : null;
    }

    /** The affine form of a body expression: a numeric atom, a newtype construct's wrapped value, or
     * {@code null}. */
    private LinearForm affineOf(Ast.Expr e, Scope scope) {
        return affine(e, n -> {
            if (n instanceof Ast.NewData nd && nd.spreads().isEmpty() && nd.inits().size() == 1
                    && nd.inits().get(0).name().equals("value")
                    && numericNewtype(Type.ref(nd.typeName().denotes()))) {
                return affineOf(nd.inits().get(0).value(), scope);
            }
            String atom = atomOf(n, scope);
            return atom == null ? null : LinearForm.atom(atom);
        });
    }

    /** The leaf rule for an invariant expression: a bare name resolves to its field/{@code value}, a
     * chain read off one to that location, and a size call over one to that container's size atom.
     * A bare name goes through the form because what a construction gives a field may be an
     * arithmetic result rather than a location; a chain read off it is a location either way. */
    private Function<Ast.Expr, LinearForm> resolveLeaf(Bindings binds) {
        return n -> {
            BigDecimal folded = clauseSizeConstant(n, binds);
            if (folded != null) {
                return LinearForm.constant(folded);
            }
            String size = clauseSizeAtom(n, binds);
            if (size != null) {
                return LinearForm.atom(size);
            }
            if (n instanceof Ast.Var v) {
                return binds.form().apply(v.name());
            }
            if (n instanceof Ast.FieldAccess) {
                String path = invPath(n, binds);
                return path == null ? null : LinearForm.atom(path);
            }
            return null;
        };
    }

    /** A container a clause names, as the term it stands for, and the rule that names that term. */
    private record Named(Ast.Expr term, Function<Ast.Expr, String> key) {}

    /** What a clause's container argument really is: the construction's own expression where the
     * clause names a field, the clause's own expression otherwise. {@code peel} takes the
     * size-keeping operations off — a size reads how many, and how the elements are made has no
     * bearing on that. */
    private Named resolve(Ast.Expr arg, Bindings binds, boolean peel) {
        Ast.Expr here = peel ? sizeSource(arg) : arg;
        Ast.Expr given = atSite(here, binds);
        if (given == null) {
            return new Named(here, siteOf(binds));
        }
        return new Named(peel ? sizeSource(given) : given, binds.bodyKey());
    }

    /** The number a size call in a clause folds to once the construction's own expression stands where
     * the clause wrote a field — {@code String.length(value)} over {@code Code("1A")} is 2 — or
     * {@code null} where it folds to none. */
    private BigDecimal clauseSizeConstant(Ast.Expr e, Bindings binds) {
        if (!(e instanceof Ast.Apply call) || !SIZE_CALLS.contains(call.reaches())
                || call.args().size() != 1) {
            return null;
        }
        Ast.Expr arg = call.args().get(0);
        Ast.Expr given = atSite(arg, binds);
        Ast.Expr container = given == null ? arg : given;
        // A list written out has as many elements as it is written with, whatever the elements are.
        if (container instanceof Ast.ListLit list) {
            return BigDecimal.valueOf(list.elements().size());
        }
        return constantNumber(new Ast.Apply(call.function(), List.of(container),
                call.origin(), call.pos()));
    }

    /** The atom a size call in a clause names, or {@code null}. */
    private String clauseSizeAtom(Ast.Expr e, Bindings binds) {
        if (!(e instanceof Ast.Apply call) || !SIZE_CALLS.contains(call.reaches()) || call.args().size() != 1) {
            return null;
        }
        Named named = resolve(call.args().get(0), binds, true);
        String key = named.key().apply(named.term());
        return key == null ? null : call.written() + "(" + key + ")";
    }

    /** The path an invariant expression names at the construction site: a bare field name through the
     * bindings, then plain field steps. */
    private String invPath(Ast.Expr e, Bindings binds) {
        // A clause is a path over the declaration's own fields, read by the very rule a body path is
        // read by — so a newtype's `.value` is the same location on both sides — and then the field it
        // is rooted at is replaced by what the construction is giving that field. One rule for what a
        // location is, applied twice, rather than two rules that have to be kept agreeing.
        String local = pathKey(e, Scope.of(binds.fields()));
        if (local == null) {
            return null;
        }
        int dot = local.indexOf('.');
        String root = dot < 0 ? local : local.substring(0, dot);
        String given = binds.path().apply(root);
        if (given == null) {
            return null;
        }
        return dot < 0 ? given : given + local.substring(dot);
    }

    private static LinearForm negate(LinearForm f) {
        return f == null ? null : f.negate();
    }

    private static LinearForm add(LinearForm a, LinearForm b, boolean subtract) {
        if (a == null || b == null) {
            return null;
        }
        return subtract ? a.minus(b) : a.plus(b);
    }

    /** The canonical atom key of a numeric location ({@code x}, {@code p.a}, a newtype's value) or of
     * a size call over a nameable container, or {@code null} if {@code e} is neither. */
    private String atomOf(Ast.Expr e, Scope scope) {
        String size = sizeAtom(e, arg -> bodyKey(arg, scope));
        if (size != null) {
            return size;
        }
        return isNumeric(typeExpr(e, scope)) ? pathKey(e, scope) : null;
    }

    /** A body expression's canonical key: a location names itself, and everything else is read
     * structurally. */
    private String bodyKey(Ast.Expr e, Scope scope) {
        return termKey(e, x -> pathKey(x, scope), Map.of(), 0);
    }

    /**
     * How a value a construction is being given is named where a clause reads it: a location names
     * itself, and a container built from one by an operation the table covers names that
     * construction. Anything else names nothing.
     *
     * <p>The restriction is what ties the flagging to what is said. A location is always named: the
     * seeding writes about locations, so a clause reading one reads something. A container built by an
     * operation the table covers is named, since the table is a rule about it. A computed value is
     * named only where a guard on this path spoke about it — then, and only then, the author has
     * stated something the clause can be read against, and leaving the construction unreported would
     * be dropping what they said.
     *
     * <p>A computed value nothing has spoken about is named by nothing, and its construction is
     * silent. That is this check's flagging policy and not a proof: the run-time check stands for the
     * whole of such an invariant. Widening it is a matter of naming more values here, which is where
     * a stated result type or a stdlib rule would enter.
     */
    private String siteKey(Ast.Expr e, Scope scope, Known k) {
        // A value written out is not something a guard can be written about: there is nothing to
        // state of `"xyz"` that the text does not already say. Where a clause reading it folds it is
        // decided before this is asked, and where it does not fold there is no guard that would
        // discharge it, so naming it here would only report what the author cannot answer.
        if (isWritten(e)) {
            return null;
        }
        String located = locationKey(e, scope);
        if (located != null) {
            return located;
        }
        String term = bodyKey(e, scope);
        if (term == null) {
            return null;
        }
        return namedByRule(e, scope) || k.speaksOf(term) ? term : null;
    }

    /** The atom key of {@code SIZE_CALL(container)} when {@code key} can name the container, else
     * {@code null}. */
    private static String sizeAtom(Ast.Expr e, Function<Ast.Expr, String> key) {
        if (!(e instanceof Ast.Apply call) || !SIZE_CALLS.contains(call.reaches()) || call.args().size() != 1) {
            return null;
        }
        String arg = key.apply(sizeSource(call.args().get(0)));
        return arg == null ? null : call.written() + "(" + arg + ")";
    }

    /** The container a size is really the size of: an operation that keeps the size of what it was
     * built from is peeled away, so {@code List.length(List.map(f, xs))} is the atom
     * {@code List.length(xs)}. How the elements are made has no bearing on how many there are, which
     * is why the closure does not enter the key. */
    private static Ast.Expr sizeSource(Ast.Expr e) {
        if (e instanceof Ast.Apply call) {
            Built built = BUILT_FROM.get(call.reaches());
            if (built != null && built.shape().keepsSize() && built.from() < call.args().size()) {
                return sizeSource(call.args().get(built.from()));
            }
        }
        return e;
    }

    /** What is known of the size of every container a clause names: never negative, and no greater
     * than the size of what it was built from wherever the building can only drop elements. */
    private void sizeFacts(Ast.Expr e, Bindings binds, List<Constraint> out) {
        if (!(e instanceof Ast.Apply call)) {
            Ast.forEachChild(e, child -> sizeFacts(child, binds, out));
            return;
        }
        if (SIZE_CALLS.contains(call.reaches()) && call.args().size() == 1) {
            Named named = resolve(call.args().get(0), binds, true);
            String atom = clauseSizeAtom(e, binds);
            if (atom != null) {
                out.add(new Constraint(LinearForm.atom(atom), Rel.GE));   // a size is never negative
                bounds(call.written(), named.term(), named.key(), out);
            }
        }
        for (Ast.Expr arg : call.args()) {
            sizeFacts(arg, binds, out);
        }
    }

    /** The same, over a body expression, where a term is only ever itself. */
    private void sizeFacts(Ast.Expr e, Scope scope, List<Constraint> out) {
        sizeFacts(e, Bindings.ofBody(x -> bodyKey(x, scope)), out);
    }

    /** {@code size(c) <= size(what c was built from)}, down the chain, wherever the building can only
     * drop elements. */
    private void bounds(String sizeCall, Ast.Expr container, Function<Ast.Expr, String> key,
                        List<Constraint> out) {
        if (!(container instanceof Ast.Apply call)) {
            return;
        }
        Built built = BUILT_FROM.get(call.reaches());
        if (built == null || built.shape().keepsSize() || built.from() >= call.args().size()) {
            return;
        }
        Ast.Expr source = sizeSource(call.args().get(built.from()));
        String here = key.apply(container);
        String there = key.apply(source);
        if (here == null || there == null) {
            return;
        }
        out.add(new Constraint(
                LinearForm.atom(sizeCall + "(" + here + ")")
                        .minus(LinearForm.atom(sizeCall + "(" + there + ")")),
                Rel.LE));
        bounds(sizeCall, source, key, out);
    }

    /** The keys a guard could have settled to establish this clause: the predicate as written, and
     * the same predicate of each container the written one was built from by a construction that
     * carries it. Stating {@code List.all(p, xs)} is stating it of every sublist of {@code xs}. */
    private List<String> factKeys(Ast.Expr inv, Bindings binds) {
        String written = siteOf(binds).apply(inv);
        if (written == null) {
            return List.of();
        }
        List<String> keys = new ArrayList<>();
        keys.add(written);
        if (!(inv instanceof Ast.Apply call)) {
            return keys;
        }
        Carried carried = CARRIED.get(call.reaches());
        if (carried == null || carried.container() >= call.args().size()) {
            return keys;
        }
        // The predicate over each container the one it names was built from — read at the site, so
        // the operations the construction wrote are the ones peeled off. The peeled container is a
        // term of the body, and the rest of the call is the clause's, so each is named by its own
        // rule and the two meet in the key.
        Named named = resolve(call.args().get(carried.container()), binds, false);
        Ast.Expr container = named.term();
        Ast.Apply stated = call;
        while (container instanceof Ast.Apply inner) {
            Built built = BUILT_FROM.get(inner.reaches());
            if (built == null || built.from() >= inner.args().size()) {
                break;
            }
            Ast.Apply next = carries(stated, carried, inner, built);
            if (next == null) {
                break;
            }
            Ast.Expr source = inner.args().get(built.from());
            String inside = named.key().apply(source);
            if (inside == null) {
                break;
            }
            String key = termKey(next, spliced(call.args().get(carried.container()), inside, binds),
                    Map.of(), 0);
            if (key == null) {
                break;
            }
            keys.add(key);
            stated = next;
            container = source;
        }
        return keys;
    }

    /**
     * The predicate as it applies to what {@code inner} was built from, or {@code null} when it does
     * not apply there. A construction the shape carries leaves the predicate as it was. A mapping
     * carries nothing on its own, but a predicate stated over a projection carries when the closure
     * copied that field across, over the field it came from.
     */
    private Ast.Apply carries(Ast.Apply stated, Carried carried, Ast.Apply inner, Built built) {
        if (carried.through().contains(built.shape())) {
            return stated;
        }
        Integer at = PROJECTION_OF.get(stated.reaches());
        if (built.shape() != Shape.MAPS || at == null || at >= stated.args().size()) {
            return null;
        }
        // Where the mapping's closure is written is already stated once, by the table that says which
        // argument each combinator hands its elements to.
        Combinator combo = COMBINATORS.get(inner.reaches());
        if (combo == null || combo.closureArg() >= inner.args().size()) {
            return null;
        }
        Ast.Expr traced = projectionThrough(stated.args().get(at), inner.args().get(combo.closureArg()));
        return traced == null ? null : withArg(stated, at, traced);
    }

    /**
     * The projection over an element that a projection over a mapped list reduces to, or
     * {@code null}.
     *
     * <p>{@code .product} over {@code List.map(r -> Line { product = r.product, ... }, xs)} is
     * {@code .product} over {@code xs}: the closure copied that field across, so two mapped elements
     * differ there exactly when the two they came from did. Bounded deliberately — a field a closure
     * computes from others is not this.
     */
    private Ast.Expr projectionThrough(Ast.Expr projection, Ast.Expr closure) {
        if (!(projection instanceof Ast.Block proj) || proj.params().size() != 1
                || !(closure instanceof Ast.Block step) || step.params().size() != 1) {
            return null;
        }
        Ast.Binder element = step.params().get(0);
        List<String> read = new Reads(proj.params().get(0).name()).chain(proj.body());
        if (read == null) {
            return null;
        }
        Reads reads = new Reads(element.name());
        Ast.Expr made = reads.produced(step.body());
        List<String> traced;
        if (read.isEmpty()) {
            traced = reads.chain(made);   // the closure hands the element straight back
        } else {
            if (!(made instanceof Ast.NewData nd) || !nd.spreads().isEmpty()) {
                return null;
            }
            List<String> copied = null;
            for (Ast.FieldInit fi : nd.inits()) {
                if (fi.name().equals(read.get(0))) {
                    copied = reads.chain(fi.value());
                }
            }
            if (copied == null) {
                return null;
            }
            traced = new ArrayList<>(copied);
            traced.addAll(read.subList(1, read.size()));
        }
        if (traced == null) {
            return null;
        }
        Ast.Expr on = Ast.Var.local(element, step.pos());
        for (String field : traced) {
            on = new Ast.FieldAccess(on, field, step.pos());
        }
        return new Ast.Block(List.of(element), on, step.pos());
    }

    /**
     * What the names in a closure read off the element it is handed: a field chain, or nothing this
     * trace can follow. A binding introduces what it reads <em>where it is written</em> — an expansion
     * splices {@code let $0_r = r in ...} into a closure, and the closure may bind over its own
     * parameter or over a name an earlier binding read — so what a name denotes is settled against the
     * bindings before it and not reread later. Keeping the expression instead and substituting by
     * spelling cannot say that: {@code let r = r} would stand for itself, which is the identity here
     * and an endless walk there.
     */
    private static final class Reads {

        private final String element;
        private final Map<String, List<String>> chains = new HashMap<>();

        private Reads(String element) {
            this.element = element;
        }

        /** The expression the body produces, with what the bindings on the way there read taken in. */
        Ast.Expr produced(Ast.Expr body) {
            Ast.Expr cur = body;
            while (cur instanceof Ast.LetIn li) {
                List<String> read = chain(li.value());
                chains.put(li.name(), read);
                cur = li.body();
            }
            return cur;
        }

        /** The chain {@code e} reads off the element, or {@code null} if it reads anything else. */
        List<String> chain(Ast.Expr e) {
            return switch (e) {
                case Ast.LetIn li -> {
                    Reads inner = new Reads(element);
                    inner.chains.putAll(chains);
                    inner.chains.put(li.name(), chain(li.value()));
                    yield inner.chain(li.body());
                }
                case Ast.FieldAccess fa -> {
                    List<String> head = chain(fa.target());
                    if (head == null) {
                        yield null;
                    }
                    List<String> out = new ArrayList<>(head);
                    out.add(fa.field());
                    yield out;
                }
                case Ast.Var v when chains.containsKey(v.name()) -> chains.get(v.name());
                case Ast.Var v -> v.name().equals(element) ? List.of() : null;
                default -> null;
            };
        }
    }

    /** The clause's naming rule with one argument already named: what lets a key hold a term of the
     * clause and a term of the body at once. */
    private Function<Ast.Expr, String> spliced(Ast.Expr at, String named, Bindings binds) {
        return e -> e == at ? named : invPath(e, binds);
    }

    private static Ast.Apply withArg(Ast.Apply call, int at, Ast.Expr arg) {
        List<Ast.Expr> args = new ArrayList<>(call.args());
        args.set(at, arg);
        return call.withArgs(args);
    }

    /** An emptiness check as the comparison it means, or {@code e} unchanged. */
    private static Ast.Expr asSizeComparison(Ast.Expr e) {
        if (e instanceof Ast.Apply call && call.args().size() == 1
                && EMPTINESS.containsKey(call.reaches())) {
            String sizeName = EMPTINESS.get(call.reaches());
            Ast.Apply size = new Ast.Apply(sizeName, new souther.compiler.types.ValueName.Stdlib(sizeName), call.args(),
                    call.origin(),
                    call.pos());
            return new Ast.Binary(Ast.BinOp.EQ, size, new Ast.IntLit(0, call.pos()), call.pos());
        }
        return e;
    }

    /**
     * The canonical key of an expression as a term, or {@code null} when nothing here can be named.
     * Two expressions with one key compute one value, which is the whole of what the fact set knows:
     * a guard and an invariant clause state the same predicate exactly when their calls key alike.
     *
     * <p>A location is asked of {@code site} — the body's path rule, or the invariant's rule for what
     * a field is being given — so the two sides meet on the construction's own names. A closure
     * parameter is keyed by where it is bound rather than by its spelling, so {@code r -> r.a} and
     * {@code row -> row.a} are one term while a free name inside the closure is still resolved
     * through {@code site} and so is part of the term. Anything outside this grammar keys as
     * {@code null}, and the clause reading it is left opaque.
     */
    private String termKey(Ast.Expr raw, Function<Ast.Expr, String> site, Map<String, String> bound,
                           int depth) {
        Ast.Expr e = asOperator(raw);
        String root = rootName(e);
        if (root != null) {
            String at = bound.get(root);
            return at != null ? chainOn(at, e) : site.apply(e);
        }
        String named = site.apply(e);
        if (named != null) {
            return named;   // a subterm the site has already named — see spliced
        }
        return switch (e) {
            case Ast.IntLit i -> Long.toString(i.value());
            case Ast.DecimalLit d -> d.value().toPlainString() + "m";
            case Ast.StringLit s -> quoted(s.value());
            case Ast.BoolLit b -> Boolean.toString(b.value());
            case Ast.Neg n -> wrap("-", termKey(n.operand(), site, bound, depth));
            case Ast.Binary b -> {
                String l = termKey(b.left(), site, bound, depth);
                String r = termKey(b.right(), site, bound, depth);
                yield l == null || r == null ? null : binaryKey(b.op(), l, r);
            }
            case Ast.ListLit l -> elementsKey("[", l.elements(), site, bound, depth, "]");
            case Ast.Tuple t -> elementsKey("(", t.elements(), site, bound, depth, ")");
            case Ast.TupleGet g -> wrap("." + g.index(), termKey(g.tuple(), site, bound, depth));
            case Ast.If iff -> elementsKey("if(", List.of(iff.cond(), iff.then(), iff.els()),
                    site, bound, depth, ")");
            case Ast.Block b -> {
                Map<String, String> inner = binding(bound, b.paramNames(), depth);
                yield wrap("\\" + b.params().size(), termKey(b.body(), site, inner, depth + 1));
            }
            case Ast.LetIn li -> {
                String value = termKey(li.value(), site, bound, depth);
                Map<String, String> inner = binding(bound, List.of(li.name()), depth);
                String body = termKey(li.body(), site, inner, depth + 1);
                yield value == null || body == null ? null : "let(" + value + ", " + body + ")";
            }
            // A construction is a pure function of its fields, and a closure that builds one is what a
            // mapping usually is. Fields are keyed in name order, so two sites writing them in
            // different orders write one term.
            case Ast.NewData nd when nd.spreads().isEmpty() -> {
                List<Ast.FieldInit> inits = new ArrayList<>(nd.inits());
                inits.sort(java.util.Comparator.comparing(Ast.FieldInit::name));
                StringBuilder sb = new StringBuilder(nd.typeName().denotes().toString()).append('{');
                for (int i = 0; i < inits.size(); i++) {
                    String v = termKey(inits.get(i).value(), site, bound, depth);
                    if (v == null) {
                        yield null;
                    }
                    sb.append(i == 0 ? "" : ", ").append(inits.get(i).name()).append('=').append(v);
                }
                yield sb.append('}').toString();
            }
            // Only the library's own functions: they are pure, so one written call is one value.
            case Ast.Apply c when Prelude.isLibraryFunction(c.reaches()) ->
                    elementsKey(c.reaches() + "(", c.args(), site, bound, depth, ")");
            default -> null;
        };
    }

    /** {@code bound} with each of {@code names} keyed by where it is bound rather than by its
     * spelling, so two expressions that differ only in what they called a binding are one term. */
    private static Map<String, String> binding(Map<String, String> bound, List<String> names, int depth) {
        Map<String, String> inner = new HashMap<>(bound);
        for (int i = 0; i < names.size(); i++) {
            inner.put(names.get(i), "#" + depth + "." + i);
        }
        return inner;
    }

    private String elementsKey(String open, List<Ast.Expr> parts, Function<Ast.Expr, String> site,
                               Map<String, String> bound, int depth, String close) {
        StringBuilder sb = new StringBuilder(open);
        for (int i = 0; i < parts.size(); i++) {
            String part = termKey(parts.get(i), site, bound, depth);
            if (part == null) {
                return null;
            }
            sb.append(i == 0 ? "" : ", ").append(part);
        }
        return sb.append(close).toString();
    }

    /**
     * A binary as a key. The six comparisons are two: {@code ==} over the pair in a settled order,
     * since which side is written first is not part of what it says, and {@code <}, with the other
     * three written as one of those denied. Two clauses comparing the same two terms are then one term
     * however the author reached for it — which matters wherever the comparison is not the whole
     * condition, since only there can the denial not be carried by the polarity instead.
     */
    private static String binaryKey(Ast.BinOp op, String l, String r) {
        return switch (op) {
            case EQ -> l.compareTo(r) <= 0 ? cmp("EQ", l, r) : cmp("EQ", r, l);
            case NE -> "!" + binaryKey(Ast.BinOp.EQ, l, r);
            case LT -> cmp("LT", l, r);
            case GT -> cmp("LT", r, l);
            case GE -> "!" + cmp("LT", l, r);
            case LE -> "!" + cmp("LT", r, l);
            default -> cmp(op.toString(), l, r);
        };
    }

    private static String cmp(String op, String l, String r) {
        return "(" + l + " " + op + " " + r + ")";
    }

    /** A string value written into a key with the punctuation the key itself uses escaped, so a value
     * holding a quote or a comma cannot be read back as a different expression. */
    private static String quoted(String value) {
        return "\"" + value.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
    }

    private static String wrap(String prefix, String inner) {
        return inner == null ? null : prefix + "(" + inner + ")";
    }

    /** The name at the head of a {@code x}/{@code x.a.b} chain, or {@code null} if {@code e} is not one. */
    private static String rootName(Ast.Expr e) {
        return switch (e) {
            case Ast.Var v -> v.name();
            case Ast.FieldAccess fa -> rootName(fa.target());
            default -> null;
        };
    }

    /** The field chain of {@code e} rebuilt on {@code head}. */
    private static String chainOn(String head, Ast.Expr e) {
        return e instanceof Ast.FieldAccess fa ? chainOn(head, fa.target()) + "." + fa.field() : head;
    }

    /** The location {@code e} is, or {@code null} where it is a computed value rather than a place.
     * The same walk {@link #pathKey} makes, asking each name for a location instead of for whatever
     * key it has — so a chain read off a computed value is computed too. */
    private String locationKey(Ast.Expr e, Scope scope) {
        return switch (e) {
            case Ast.Var v -> scope.denotes(v.name()) instanceof Denotes.Location loc ? loc.key() : null;
            case Ast.FieldAccess fa -> {
                Type owner = typeExpr(fa.target(), scope);
                if (fa.field().equals("value") && TypeOps.isSingleValueNewtype(owner, symbols)) {
                    yield locationKey(fa.target(), scope);
                }
                String base = locationKey(fa.target(), scope);
                yield base == null ? null : base + "." + fa.field();
            }
            default -> null;
        };
    }

    /**
     * What a binding's initializer denotes: the location it is where it is one, else the term it
     * computes, else nothing. A name is an alias and never a value of its own — this is the one place
     * that decides it, so an expression answers the same whether it was written where it is used or
     * given a name first.
     */
    private Denotes denotationOf(Ast.Expr e, Scope scope) {
        String located = locationKey(e, scope);
        if (located != null) {
            return new Denotes.Location(located);
        }
        String term = bodyKey(e, scope);
        return term == null ? new Denotes.Nothing() : new Denotes.Term(term, namedByRule(e, scope));
    }

    /** Whether {@code e} is a value written out rather than computed from anything. */
    private static boolean isWritten(Ast.Expr e) {
        return e instanceof Ast.IntLit || e instanceof Ast.DecimalLit || e instanceof Ast.StringLit
                || e instanceof Ast.BoolLit;
    }

    /** Whether {@code e} is a container built by an operation the preservation table covers, over an
     * argument that is itself named. */
    private boolean builtByRule(Ast.Expr e, Scope scope) {
        if (!(e instanceof Ast.Apply call)) {
            return false;
        }
        Built built = BUILT_FROM.get(call.reaches());
        return built != null && built.from() < call.args().size()
                && namedByRule(call.args().get(built.from()), scope);
    }

    /**
     * Whether {@code e} names something without a guard having to have spoken about it: it is read all
     * the way down. A location is; so is a value composed of ones by a shape the term grammar reads —
     * a concatenation, a conditional, arithmetic, a container the preservation table covers. A call
     * the check has no rule about is not, and neither is anything built from one: nothing follows from
     * naming it, and its construction is left to the run-time check.
     */
    private boolean namedByRule(Ast.Expr e, Scope scope) {
        if (locationKey(e, scope) != null) {
            return true;
        }
        if (e instanceof Ast.Var v) {
            return scope.denotes(v.name()) instanceof Denotes.Term t && t.byRule();
        }
        Ast.Expr read = asOperator(e);
        if (read instanceof Ast.Apply call && !readsAsATerm(call)) {
            return builtByRule(read, scope);
        }
        // Arithmetic is the numeric domain's to name. Where the domain builds a form, that form is
        // what a clause is read against; where it declines to — a variable product, an integer divide
        // — declining is a decision about what this check reasons over, and reporting a construction
        // it has decided not to reason over would be reporting the decision as the author's to fix.
        if (read instanceof Ast.Binary bin && isArith(bin.op())) {
            return false;
        }
        // A conditional is one of its branches and which one is not decided here. Saying only that it
        // is that term reports every construction over one, including where both branches satisfy the
        // clause. Reading it is checking the construction on each branch under its own condition,
        // which this walk does not do, so it is not named until it does.
        if (read instanceof Ast.If) {
            return false;
        }
        boolean[] all = {true};
        // A closure is not part of what names the value: the tables are rules about how many elements
        // there are and where they came from, and how each one is made has no bearing on either.
        Ast.forEachChild(read, child -> all[0] = all[0]
                && (child instanceof Ast.Block || namedByRule(child, scope)));
        return all[0];
    }

    /** Whether the check has a rule about what a call answers, rather than only about how to render it. */
    private static boolean readsAsATerm(Ast.Apply call) {
        return SIZE_CALLS.contains(call.reaches()) || BUILT_FROM.containsKey(call.reaches())
                || CARRIED.containsKey(call.reaches()) || QUANTIFIERS.contains(call.reaches())
                || "Bool.not".equals(call.reaches());
    }

    private String pathKey(Ast.Expr e, Scope scope) {
        return switch (e) {
            // a name given a location is that location, as a newtype's `.value` is its own
            case Ast.Var v -> scope.keyOf(v.name());
            case Ast.FieldAccess fa -> {
                Type owner = typeExpr(fa.target(), scope);
                if (fa.field().equals("value") && TypeOps.isSingleValueNewtype(owner, symbols)) {
                    yield pathKey(fa.target(), scope);   // a newtype's .value is the same location
                }
                String base = pathKey(fa.target(), scope);
                yield base == null ? null : base + "." + fa.field();
            }
            default -> null;
        };
    }

    /** What is known after a binding takes over {@code name}: everything that mentioned it is dropped,
     * because the name now denotes something else. The test is on the key's text and errs towards
     * dropping — a term that merely reads like it mentions the name loses a fact it could have kept,
     * which costs precision and never soundness. */
    private static Known rebind(Known k, String name) {
        return k.forgetIf(key -> mentions(key, name));
    }

    /** Whether {@code key} contains {@code name} as a whole identifier. */
    private static boolean mentions(String key, String name) {
        for (int i = key.indexOf(name); i >= 0; i = key.indexOf(name, i + 1)) {
            int end = i + name.length();
            boolean left = i == 0 || !Character.isUnicodeIdentifierPart(key.charAt(i - 1));
            boolean right = end == key.length() || !Character.isUnicodeIdentifierPart(key.charAt(end));
            if (left && right) {
                return true;
            }
        }
        return false;
    }

    // --- a minimal local typer (enough for atom/affine detection) ------------------------------

    private Type typeExpr(Ast.Expr raw, Scope scope) {
        Ast.Expr e = asOperator(raw);
        return switch (e) {
            case Ast.IntLit _ -> Type.INT;
            case Ast.DecimalLit _ -> Type.DECIMAL;
            case Ast.Var v -> scope.typeOf(v.name());
            case Ast.FieldAccess fa -> {
                Type owner = typeExpr(fa.target(), scope);
                yield owner instanceof Type.Ref r && symbols.get(r.name()) instanceof Ast.Data d
                        ? TypeOps.fieldTypes(d, symbols).get(fa.field()) : null;
            }
            case Ast.NewData nd -> Type.ref(nd.typeName().denotes());
            case Ast.LetIn li -> {
                Type bound = typeExpr(li.value(), scope);
                yield typeExpr(li.body(),
                        scope.binding(li.name(), bound, denotationOf(li.value(), scope)));
            }
            case Ast.Neg n -> typeExpr(n.operand(), scope);
            case Ast.Binary b when isArith(b.op()) -> arithType(b, scope);
            default -> null;
        };
    }

    /** The result type of an arithmetic binary: the newtype for closed {@code +}/{@code -}
     * (via the checker's shared rule), else the numeric base, else {@code null}. */
    private Type arithType(Ast.Binary b, Scope scope) {
        Type lt = typeExpr(b.left(), scope);
        Type rt = typeExpr(b.right(), scope);
        // Closed `+`/`-` and scalar `*`/`/` both yield the newtype (the checker has already validated
        // admissibility, so a newtype operand here means the result is that newtype).
        if (isArith(b.op())) {
            Type nt = TypeOps.closedNewtypeArithResult(lt, rt, symbols);
            if (nt != null) {
                return nt;
            }
        }
        if (lt == Type.INT || lt == Type.DECIMAL) {
            return lt;
        }
        return rt == Type.INT || rt == Type.DECIMAL ? rt : null;
    }

    /** What a container hands its closure: a list's or set's element, a map's value (the key is the
     * other closure parameter and is not the one the table credits), an option's payload. */
    private static Type elementType(Type t) {
        if (t instanceof Type.ListOf list) {
            return list.element();
        }
        if (t instanceof Type.SetOf set) {
            return set.element();
        }
        if (t instanceof Type.MapOf map) {
            return map.value();
        }
        if (t instanceof Type.OptionOf opt) {
            return opt.element();
        }
        return null;
    }

    private boolean numericNewtype(Type t) {
        return TypeOps.directNumericNewtypeBase(t, symbols) != null;
    }

    private boolean isNumeric(Type t) {
        return t == Type.INT || t == Type.DECIMAL || numericNewtype(t);
    }

    // --- helpers -------------------------------------------------------------------------------

    private static boolean isArith(Ast.BinOp op) {
        return op == Ast.BinOp.ADD || op == Ast.BinOp.SUB || op == Ast.BinOp.MUL || op == Ast.BinOp.DIV;
    }

    private static Rel relOf(Ast.BinOp op) {
        return switch (op) {
            case GE -> Rel.GE;
            case GT -> Rel.GT;
            case LE -> Rel.LE;
            case LT -> Rel.LT;
            case EQ -> Rel.EQ;
            case NE -> Rel.NE;
            default -> null;
        };
    }

    private static Rel negateRel(Rel rel) {
        return switch (rel) {
            case GE -> Rel.LT;
            case GT -> Rel.LE;
            case LE -> Rel.GT;
            case LT -> Rel.GE;
            case EQ -> Rel.NE;
            case NE -> Rel.EQ;
        };
    }
}
