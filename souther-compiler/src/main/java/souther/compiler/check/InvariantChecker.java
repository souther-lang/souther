package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.check.NumericDomain.LinearForm;
import souther.compiler.check.NumericDomain.Rel;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The intraprocedural invariant-discharge check (spec §invariant-discharge). It walks a behavior's
 * body threading what the guards have settled — a {@link NumericDomain} of relations and a
 * {@link PredicateFacts} of everything that states no relation — seeded from the input types'
 * invariants and refined along each {@code guard}/{@code if} guard (a {@code guard} is already an
 * {@code if} here). At every construction whose invariant it can carry, it asks whether the guards
 * <em>discharge</em> it. A construction proven to violate its invariant on a reachable path is a
 * compile error (the path-sensitive generalization of the constant check {@code Amount(-5)}); one it
 * cannot prove is a warning (a possible abort — guard it, or reify the relation into a type
 * invariant). An invariant naming something it cannot name is left opaque (no diagnostic; the
 * run-time check stays), so every flagged construction has a guard that discharges it.
 *
 * <p>What it reads is Core: the body in the representation the rules are written at
 * ({@link InliningPolicy#DISCHARGE}), typed by the checker like any other, and each declaration's
 * invariant typed the same way against the fields it is written over. A clause is then read at a
 * construction by putting the value each field is being given where that field is read — one
 * expression in one representation, so what a clause says and what the body says meet as terms
 * rather than as two spellings that have to be kept agreeing.
 *
 * <p>Which value a fact is about is the binding a name was answered with ({@link Location}), so a
 * body that binds one spelling twice states two things and nothing has to be forgotten when it does.
 *
 * <p>The walk mirrors {@link TotalityChecker}: a {@code switch} over {@link Core} threading an
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

    /** The library operation written {@code qualified}, as what a name reaching it denotes. */
    private static ValueName op(String qualified) {
        return new ValueName.Stdlib(qualified);
    }

    /** A stdlib combinator whose closure (argument {@code closureArg}) is handed each element of its
     * container argument ({@code listArg}) as closure parameter {@code elementParam} — mirrors
     * {@link TotalityChecker}'s table, so a construction inside a {@code List.map} or
     * {@code List.foldFrom} closure is analyzed with the element bound to the container's element type
     * ({@link #elementType}).
     *
     * <p>A rule is keyed by the operation a call reaches when this tree is read, which is not every
     * name an author can write: {@code List.fold} is rewritten to {@code List.foldFrom} before any of
     * this, so a rule under that name could not be looked up. {@code InvariantCombinatorRulesTest}
     * holds the table to both halves of that — every name survives the rewrite, and every name has a
     * program that fires it. */
    private record Combinator(int closureArg, int elementParam, int listArg) {}

    private static final Map<ValueName, Combinator> COMBINATORS = Map.ofEntries(
            Map.entry(op("List.foldFrom"), new Combinator(0, 1, 2)),
            Map.entry(op("List.foldr"), new Combinator(0, 1, 2)),
            Map.entry(op("List.map"), new Combinator(0, 0, 1)),
            Map.entry(op("List.filter"), new Combinator(0, 0, 1)),
            Map.entry(op("List.all"), new Combinator(0, 0, 1)),
            Map.entry(op("List.any"), new Combinator(0, 0, 1)),
            Map.entry(op("List.find"), new Combinator(0, 0, 1)),
            Map.entry(op("List.partition"), new Combinator(0, 0, 1)),
            Map.entry(op("List.concatMap"), new Combinator(0, 0, 1)),
            Map.entry(op("List.filterMap"), new Combinator(0, 0, 1)),
            Map.entry(op("List.sortBy"), new Combinator(0, 0, 1)),
            Map.entry(op("List.groupBy"), new Combinator(0, 0, 1)),
            Map.entry(op("List.indexBy"), new Combinator(0, 0, 1)),
            Map.entry(op("List.allUniqueBy"), new Combinator(0, 0, 1)),
            Map.entry(op("List.indexedMap"), new Combinator(0, 1, 1)),
            Map.entry(op("Map.fold"), new Combinator(0, 2, 2)),
            Map.entry(op("Map.map"), new Combinator(0, 1, 1)),
            Map.entry(op("Map.filter"), new Combinator(0, 1, 1)),
            Map.entry(op("Map.update"), new Combinator(1, 0, 2)),
            Map.entry(op("Map.upsert"), new Combinator(2, 0, 3)),
            Map.entry(op("Set.fold"), new Combinator(0, 1, 2)),
            Map.entry(op("Set.map"), new Combinator(0, 0, 1)),
            Map.entry(op("Set.filter"), new Combinator(0, 0, 1)),
            Map.entry(op("Set.partition"), new Combinator(0, 0, 1)),
            Map.entry(op("Option.map"), new Combinator(0, 0, 1)));

    /** The operations the table has a rule for, for the test that holds it to being reachable. */
    static Set<String> combinatorNames() {
        Set<String> names = new LinkedHashSet<>();
        COMBINATORS.keySet().forEach(operation -> names.add(operation.name()));
        return names;
    }

    /** The pure, total stdlib calls whose result is a number the domain can name: the size of a
     * container or a string. Each becomes an atom keyed by the call written over its argument's path
     * — {@code List.length(b.items)} — so an invariant clause and a guard naming the same container
     * name the same atom, and the guard discharges the clause. The argument must be a nameable path:
     * {@code List.length(List.map(f, xs))} is not this atom, and nothing relates the two. */
    private static final Set<ValueName> SIZE_CALLS = Set.of(
            op("List.length"), op("String.length"), op("Set.size"), op("Map.size"));

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

    private static final Map<ValueName, Built> BUILT_FROM = Map.ofEntries(
            Map.entry(op("List.reverse"), new Built(0, Shape.PERMUTES)),
            Map.entry(op("List.sort"), new Built(0, Shape.PERMUTES)),
            Map.entry(op("List.sortBy"), new Built(1, Shape.PERMUTES)),
            Map.entry(op("List.map"), new Built(1, Shape.MAPS)),
            Map.entry(op("List.indexedMap"), new Built(1, Shape.MAPS)),
            Map.entry(op("Map.map"), new Built(1, Shape.MAPS)),
            Map.entry(op("List.filter"), new Built(1, Shape.SUBSET)),
            Map.entry(op("List.distinct"), new Built(0, Shape.SUBSET)),
            Map.entry(op("List.take"), new Built(1, Shape.SUBSET)),
            Map.entry(op("List.drop"), new Built(1, Shape.SUBSET)),
            Map.entry(op("Set.filter"), new Built(1, Shape.SUBSET)),
            Map.entry(op("Map.filter"), new Built(1, Shape.SUBSET)),
            Map.entry(op("List.filterMap"), new Built(1, Shape.COLLAPSES)),
            Map.entry(op("Set.map"), new Built(1, Shape.COLLAPSES)));

    /** Where a predicate reads its container, and which shapes of construction carry it there.
     * {@code List.all} holds of any sublist of a list it holds of; {@code List.member} does not, and
     * neither survives a mapping — what a mapped element is, the mapping alone does not say. */
    private record Carried(int container, Set<Shape> through) {}

    /** Where a predicate reads the projection it is stated over. A mapping keeps a projection when
     * the closure copies that field from the element unchanged, so the predicate holds of the mapped
     * list exactly when it holds of what was mapped, over the field it came from. */
    private static final Map<ValueName, Integer> PROJECTION_OF = Map.of(op("List.allUniqueBy"), 0);

    private static final Map<ValueName, Carried> CARRIED = Map.of(
            op("List.all"), new Carried(1, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            op("List.allUniqueBy"), new Carried(1, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            op("List.any"), new Carried(1, Set.of(Shape.PERMUTES)),
            op("List.member"), new Carried(1, Set.of(Shape.PERMUTES)),
            op("Set.contains"), new Carried(1, Set.of(Shape.PERMUTES)),
            op("Map.containsKey"), new Carried(1, Set.of(Shape.PERMUTES)));

    /** The calls that state their predicate of <em>every</em> element, so what they say of a
     * container is what holds of each element a closure is handed. Which argument is the predicate
     * and which the container is what {@link #COMBINATORS} already answers of any combinator, and how
     * far the statement travels is what {@link #CARRIED} already answers of any predicate — so a
     * quantifier is the name and nothing else. {@code List.all} is the only one the library has. */
    private static final Set<ValueName> QUANTIFIERS = Set.of(op("List.all"));

    /** How many conditionals a construction opens before the rest is left to the run-time check.
     * Each one doubles the paths, and a value written over three of them is not what the bound is
     * protecting against so much as what it declines to spend the time on. */
    private static final int BRANCHES_OPENED = 3;

    /** Emptiness, by the size call it means. This is not a rule about what an operation does to a
     * property (spec §invariant-discharge-preservation) but about what a predicate <em>says</em>:
     * {@code List.isEmpty(xs)} and {@code List.length(xs) == 0} are one statement, so a guard writing
     * either discharges a clause writing the other. Without it the two would be unrelated, which is
     * an accident of which one the author reached for. */
    private static final Map<ValueName, ValueName> EMPTINESS = Map.of(
            op("List.isEmpty"), op("List.length"),
            op("Set.isEmpty"), op("Set.size"),
            op("Map.isEmpty"), op("Map.size"),
            op("String.isEmpty"), op("String.length"));

    /**
     * The library's function forms of the arithmetic operators, and the operator each one is. They
     * reach the same kernel in the same argument order — {@code Int.add} is {@code IntMath.addExact},
     * which is what {@code +} emits — so the two spellings compute one value and are read as one term.
     * {@code divide} is absent: it answers a union rather than a number.
     */
    private static final Map<ValueName, Ast.BinOp> OPERATOR_CALLS = Map.of(
            op("Int.add"), Ast.BinOp.ADD,
            op("Int.subtract"), Ast.BinOp.SUB,
            op("Int.multiply"), Ast.BinOp.MUL,
            op("Decimal.add"), Ast.BinOp.ADD,
            op("Decimal.subtract"), Ast.BinOp.SUB,
            op("Decimal.multiply"), Ast.BinOp.MUL);

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
     * relation as the clause it was written as, so it can be read again at the element a combinator's
     * closure is handed.
     *
     * <p>{@code through} is how far it travels: a construction of one of those shapes holds only
     * elements of what it was built from, so what was stated of the source still holds of each of
     * them. The predicate is kept as the block it is, already read where the relation was stated, so
     * every name in it means there what it meant there.
     */
    private record Quantified(String container, Set<Shape> through, Core.Block predicate) {}

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
            return new Known(numbers, facts, quantified, all);
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
    }

    /**
     * What the body's bindings mean where the walk is.
     *
     * <p>A binding given a location <em>is</em> that location — the rule {@link Location} carries for
     * a newtype's {@code .value}, read here of a binding instead of a field. It is what lets a
     * construction survive being moved into a helper: an expansion binds each argument and answers
     * the parameter's reads with that binding (see {@link HelperInliner}), so without it the body of
     * a helper taking a record names locations the seeding never wrote, and everything an input's
     * type guarantees stops at the call.
     *
     * <p>Nothing here is ever taken away. A binding is what it is, and a second binding of the same
     * spelling is a second binding, so a fact about the first stays true of the first and nothing
     * reads it under the second.
     */
    private record Denotations(Map<BindingId, Denotes> what, Map<BindingId, Core> values) {

        static Denotations none() {
            return new Denotations(Map.of(), Map.of());
        }

        /** What {@code binding} denotes, which is the location it is unless it was given something
         * else. */
        Denotes of(BindingId binding) {
            Denotes given = what.get(binding);
            return given != null ? given : new Denotes.At(Location.of(binding));
        }

        /** The value {@code binding} was given, or null where nothing recorded one. */
        Core valueOf(BindingId binding) {
            return values.get(binding);
        }

        Denotations binding(BindingId binding, Core value, Denotes denotes) {
            Map<BindingId, Denotes> next = new HashMap<>(what);
            next.put(binding, denotes);
            Map<BindingId, Core> bound = new HashMap<>(values);
            if (value != null) {
                bound.put(binding, value);
            }
            return new Denotations(Map.copyOf(next), Map.copyOf(bound));
        }
    }

    /**
     * What a binding denotes. A location is somewhere the seeding can have written about and a clause
     * can have named; a term is a value known only by what computes it. Merging those two would put a
     * computed value where a location is expected, which is the shape of a {@code let} answering
     * differently from the expression it was given. A written value is apart from both because what
     * it is has to travel with the name, and nothing is apart because only a term is assigned a form.
     */
    private sealed interface Denotes {

        /** The key this is known by, or {@code null} where it is known by none. */
        String key();

        /** A place: a parameter, a field chain, or another location a binding was given. */
        record At(Location where) implements Denotes {

            @Override
            public String key() {
                return where.toString();
            }
        }

        /**
         * A value named by the expression that computes it. {@code readable} is true where there is
         * something to say of it however it is reached — a form the numeric domain built, or a rule
         * about how it was made; false where only a guard naming it makes a clause readable against
         * it.
         */
        record Term(String key, boolean readable) implements Denotes {}

        /**
         * A value written out, kept as what was written. There is no guard an author could add about
         * it, so it is never named at a construction; what it is, though, still has to travel with
         * the name, or the same text would fold where it is written and not where it is bound.
         */
        record Written(String key, Core value) implements Denotes {}

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
        // Read over the declaration's own fields, each standing for itself: a construction hands one
        // value per field, so a clause naming a field names something wherever it is built.
        Core stated = c.typed(clause, data);
        List<Clause> owed;
        try {
            owed = stated == null ? null
                    : c.obligations(stated, Known.top(), Denotations.none(), false);
        } catch (RuntimeException _) {
            owed = null;   // fail-open, as the walk is
        }
        if (owed == null || owed.isEmpty()) {
            return ClauseDischarge.runtimeOnly(at, c.whyUnreadable(stated));
        }
        for (Clause owe : owed) {
            if (owe.numeric() != null) {
                return ClauseDischarge.derivable(at);
            }
        }
        return ClauseDischarge.exactMatch(at);
    }

    /** What in {@code clause} the check cannot read, said so an author can act on it. */
    private String whyUnreadable(Core clause) {
        if (clause == null) {
            return "it is not a rule this check could read as one expression";
        }
        Core blocked = unreadable(clause);
        if (blocked instanceof Core.PreservedCall call) {
            return "it calls `" + call.operation().name()
                    + "`, which the check reads as a value and not as a term";
        }
        if (blocked != null) {
            return "it is not one of the shapes the check reads";
        }
        return "it names a term the check cannot name";
    }

    /** The innermost part of {@code e} the term grammar cannot read, or {@code null} if it reads all
     * of it. Every location is granted, so what is left is the shape. */
    private Core unreadable(Core e) {
        Core[] found = {null};
        Core.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = unreadable(child);
            }
        });
        if (found[0] != null) {
            return found[0];
        }
        return termKey(e, Denotations.none(), Map.of(), 0) == null ? e : null;
    }

    /**
     * Analyzes one behavior body against the bindings its inputs are. Never throws. A {@code null}
     * body is one the analysis representation could not be built or typed for, and is not analyzed at
     * all.
     */
    static Findings analyze(Core body, Map<TypeName, List<Ast.InvariantClause>> invariants,
                            Scope params, Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols, invariants);
        if (body == null) {
            return new Findings(c.errors, c.warnings);
        }
        try {
            Known k = Known.top();
            for (Map.Entry<BindingId, Scope.Binding> p : params.bindings().entrySet()) {
                k = c.seedAt(new Core.Read(p.getValue().name(), p.getKey(), p.getValue().type(),
                        body.pos()), k, Denotations.none(), 0);
            }
            c.walk(body, k, Denotations.none(), 0);
        } catch (RuntimeException _) {
            // fail-open: the run-time invariant check remains the backstop
        }
        return new Findings(c.errors, c.warnings);
    }

    // --- the walk ------------------------------------------------------------------------------

    private void walk(Core e, Known k, Denotations at, int depth) {
        Core.If value = conditionalValueIn(e);
        if (value != null && depth < BRANCHES_OPENED) {
            // A conditional in a value position is one of its two branches, and which one is decided
            // by its condition. So this is read once with each standing there, under that condition,
            // and what the two readings find is said once. Every place a conditional can be given —
            // to a field, to a name, to a guard — is this one place.
            walk(value.cond(), k, at, depth);
            String same = bodyKey(value, at);
            say(reading(without(e, value, same, value.then(), at),
                            assumeCond(value.cond(), k, at, true), at, depth),
                    reading(without(e, value, same, value.els(), at),
                            assumeCond(value.cond(), k, at, false), at, depth));
            return;
        }
        checkIfConstruction(e, k, at, false);
        switch (e) {
            case Core.If iff -> {
                walk(iff.cond(), k, at, depth);
                walk(iff.then(), assumeCond(iff.cond(), k, at, true), at, depth);
                walk(iff.els(), assumeCond(iff.cond(), k, at, false), at, depth);
            }
            case Core.IfConstructed ic -> {
                // The attempt's own construction cannot abort — a failing invariant is the else
                // branch — so it is checked for a decided violation and never warned about as a
                // possible one. Its field values are walked on their own so a construction nested
                // inside an argument is still an ordinary, aborting one.
                checkIfConstruction(ic.construct(), k, at, true);
                Core.forEachChild(ic.construct(), child -> walk(child, k, at, depth));
                // The attempt built the value, so the binding is that construction and no location
                Known k2 = seedAt(read(ic.binder(), ic.construct().type(), ic.pos()), k, at, 0);
                walk(ic.then(), k2, at, depth);
                // Each departure stands where the invariant did not hold, and nothing was built
                // there, so none of them is seeded with anything the attempt would have guaranteed.
                ic.els().forEach(arm -> walk(arm.body(), k, at, depth));
            }
            case Core.LetIn li -> {
                // A closure is read where it is applied: what its parameter holds is decided there,
                // and reading it here would read every construction in it with the element unknown.
                if (!(li.value() instanceof Core.Block)) {
                    walk(li.value(), k, at, depth);
                }
                // The name is an alias for what its initializer denotes, so what is recorded about it
                // is recorded under that denotation and not under the binding. Recording it under the
                // binding is what made a named subexpression a term of its own, answering differently
                // from the very expression it was given.
                Denotes what = denotationOf(li.value(), at, k);
                Known k2 = k;
                // A binding that denotes what it was given is an alias and introduces no value, so
                // there is nothing to record of it: what holds of what it names already holds.
                // Recording it anyway assigns that name its own form, and an assignment drops what
                // was known of what it assigns to — the bound on it would be lost to the copy. A
                // location is always this; a term is where the form is that term's own atom.
                if (what instanceof Denotes.Term term && isNumeric(li.value().type())) {
                    LinearForm vf = affineOf(li.value(), at, k);
                    if (vf != null && !vf.equals(LinearForm.atom(term.key()))) {
                        k2 = k2.with(k2.numbers().assign(term.key(), vf));
                    }
                }
                walk(li.body(), k2, at.binding(li.binder().id(), li.value(), what), depth);
            }
            case Core.Match m -> {
                walk(m.scrutinee(), k, at, depth);
                for (Core.Case c : m.cases()) {
                    // A sum has no fields of its own, so the scrutinee is not a location any clause
                    // could have named — the case's value names only itself.
                    walk(c.body(), k, at, depth);
                }
            }
            case Core.PreservedCall call -> walkCall(call, k, at, depth);
            default -> Core.forEachChild(e, child -> walk(child, k, at, depth));
        }
    }

    /** Walks a call the representation kept standing, binding a combinator closure's element
     * parameter to the container's element type (and seeding its invariant) so a construction inside
     * the closure is analyzed rather than left opaque. */
    private void walkCall(Core.PreservedCall call, Known k, Denotations at, int depth) {
        Combinator combo = COMBINATORS.get(call.operation());
        for (int i = 0; i < call.args().size(); i++) {
            Core arg = call.args().get(i);
            Core.Block step = combo != null && i == combo.closureArg() ? blockOf(arg, at) : null;
            if (step != null && combo.elementParam() < step.params().size()
                    && combo.listArg() < call.args().size()) {
                Core container = call.args().get(combo.listArg());
                Type elem = elementType(container.type());
                // The container is read where the call is written, so what is known of its elements
                // is looked up before the closure's parameter stands for anything.
                List<Quantified> relations = elementRelations(container, k, at);
                Core element = read(step.params().get(combo.elementParam()), elem, step.pos());
                // an element of a container is not a location the body can otherwise name
                Known k2 = seedAt(element, k, at, 0);   // the element carries its type's invariant
                for (Quantified q : relations) {
                    k2 = instantiate(q, element, k2, at);
                }
                walk(step.body(), k2, at, depth);
            } else {
                walk(arg, k, at, depth);
            }
        }
    }

    /** The relations known of every element of {@code container}: those stated of it as written, and
     * those stated of a container it was built from that travel every construction in between. */
    private List<Quantified> elementRelations(Core container, Known k, Denotations at) {
        List<Quantified> found = new ArrayList<>();
        Set<Shape> crossed = EnumSet.noneOf(Shape.class);
        Core source = container;
        while (true) {
            String key = bodyKey(source, at);
            if (key != null) {
                for (Quantified q : k.quantified()) {
                    if (key.equals(q.container()) && q.through().containsAll(crossed)) {
                        found.add(q);
                    }
                }
            }
            if (!(source instanceof Core.PreservedCall call)) {
                return found;
            }
            Built built = BUILT_FROM.get(call.operation());
            if (built == null || built.from() >= call.args().size()) {
                return found;
            }
            crossed.add(built.shape());
            source = call.args().get(built.from());
        }
    }

    /** What {@code q} says of the value at {@code element}, taken into {@code k}. The predicate is
     * read again with the quantifier's own parameter standing for that element — the same reading
     * {@link #seedAt} does of a type's invariant, over the clause a quantifier holds. A relation the
     * predicate in turn states of a container is recorded, so a container of containers reaches its
     * innermost element. */
    private Known instantiate(Quantified q, Core element, Known k, Denotations at) {
        Core stated = substituted(q.predicate().body(),
                Map.of(q.predicate().params().get(0).id(), element));
        List<Quantified> nested = new ArrayList<>();
        quantifiedBy(stated, at, true, nested);
        return assume(obligations(stated, k, at, false), k).and(nested);
    }

    /** What {@code e}, asserted with polarity {@code positive}, says of every element of a container.
     * Mirrors {@link #obligations}: a conjunction states each of its sides, and a negation flips the
     * polarity. Only a stated quantifier is recorded — denying one says some element fails the
     * predicate, and which one is not something this check can name. */
    private void quantifiedBy(Core raw, Denotations at, boolean positive, List<Quantified> out) {
        Core e = asSizeComparison(raw);
        if (e instanceof Core.Binary b && b.op() == Ast.BinOp.AND && positive) {
            quantifiedBy(b.left(), at, true, out);
            quantifiedBy(b.right(), at, true, out);
            return;
        }
        Core under = negated(e);
        if (under != null) {
            quantifiedBy(under, at, !positive, out);
            return;
        }
        if (!positive || !(e instanceof Core.PreservedCall call)
                || !QUANTIFIERS.contains(call.operation())) {
            return;
        }
        Combinator over = COMBINATORS.get(call.operation());
        Carried carried = CARRIED.get(call.operation());
        if (over == null || carried == null || over.closureArg() >= call.args().size()
                || over.listArg() >= call.args().size()) {
            return;
        }
        Core.Block p = blockOf(call.args().get(over.closureArg()), at);
        if (p == null || p.params().size() != 1) {
            return;
        }
        String container = bodyKey(call.args().get(over.listArg()), at);
        if (container == null) {
            return;
        }
        out.add(new Quantified(container, carried.through(), p));
    }

    // --- construction detection & discharge check ----------------------------------------------

    private void checkIfConstruction(Core e, Known k, Denotations at, boolean attempted) {
        if (e instanceof Core.NewData nd && nd.spreads().isEmpty()) {
            if (symbols.get(nd.typeName()) instanceof Ast.Data type) {
                report(nd, type, nd.pos(), attempted, verdictOf(nd, type, k, at));
            }
            return;
        }
        // Closed arithmetic over a newtype builds one where it stands: the operands are unwrapped,
        // the operator applied, and the result constructed again, so the invariant is owed here.
        if (asOperator(e) instanceof Core.Binary bin && isArith(bin.op())
                && bin.type() instanceof Type.Ref r
                && symbols.get(r.name()) instanceof Ast.Data type && type.newtype()) {
            BindingId value = fieldBindingsOf(type).get("value");
            if (value != null && affineOf(bin, at, k) != null) {
                report(bin, type, bin.pos(), attempted,
                        verdictOf(r.name(), type, Map.of(value, bin), k, at, true));
            }
        }
    }

    /**
     * The verdict for one construction, over what each field is being given. A conditional never
     * reaches here: the walk opens it before anything is checked, so what a field is given is a
     * value and not a choice of two.
     */
    private Verdict verdictOf(Core.NewData nd, Ast.Data type, Known k, Denotations at) {
        Map<String, BindingId> fields = fieldBindingsOf(type);
        Map<BindingId, Core> given = new HashMap<>();
        for (Core.FieldInit fi : nd.inits()) {
            BindingId field = fields.get(fi.name());
            if (field == null) {
                continue;
            }
            // A name given a value written out hands over that value: the clause folds over what
            // was written, wherever the writing was done.
            Core written = writtenValue(fi.value(), at);
            given.put(field, written != null ? written : fi.value());
        }
        return verdictOf(nd.typeName(), type, given, k, at, !constantlyBuilt(type, nd));
    }

    /** Which of the values a construction hands over is not one a clause may be read against
     * ({@link #siteKey}) — by identity, since it is these very values that stand in the clause. */
    private Set<Core> unnamed(Collection<Core> given, Known k, Denotations at) {
        Set<Core> out = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Core value : given) {
            if (siteKey(value, at, k) == null) {
                out.add(value);
            }
        }
        return out;
    }

    /** Whether {@code e} is, or names, one of {@code values}. */
    private static boolean names(Core e, Set<Core> values) {
        if (values.contains(e)) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] = found[0] || names(child, values));
        return found[0];
    }

    /**
     * How a construction came out. A construction is checked before it is reported so that one
     * written over a conditional can be checked on each branch and answered once — which of the two
     * values it is is not decided here, so what holds of the construction is what holds of both.
     */
    private enum Verdict {
        /** Every clause is discharged, or none of them is expressible. */
        PROVED,
        /** A clause is expressible and unproven: the construction may abort. */
        UNKNOWN,
        /** A clause is proven to fail on a path that is reached. */
        REFUTED;

        /**
         * What holds of a value that is one of two. It is discharged where both are, and it is proven
         * to fail only where both fail — a construction one branch satisfies does not definitely
         * violate, whichever branch is taken. Everything else is possible and unproven.
         *
         * <p>A branch nothing reaches finds nothing to combine: {@link #reading} answers it with no
         * findings at all, and a position only one branch found is read as discharged on the other.
         */
        static Verdict of(Verdict a, Verdict b) {
            return a == b ? a : UNKNOWN;
        }
    }

    /** The discharge verdict for a construction of {@code type} whose fields are being given
     * {@code given}. */
    private Verdict verdictOf(TypeName named, Ast.Data type, Map<BindingId, Core> given, Known k,
                              Denotations at, boolean decidesFalse) {
        List<Ast.InvariantClause> invs = invariantsOf(named, type);
        if (invs.isEmpty()) {
            return Verdict.PROVED;
        }
        // What the construction hands over that no clause may be read against. A clause naming one of
        // them is left to the run-time check, and one that is decided outright is still decided: what
        // cannot be guarded is not the same as what cannot be computed.
        Set<Core> unnamed = unnamed(given.values(), k, at);
        List<Clause> owed = new ArrayList<>();
        for (Ast.InvariantClause inv : invs) {
            // A newtype construction from a value written out is the constant check's to report: it
            // names the clause that failed. It reads the construction as written, so a name given the
            // value is not one it sees, and this check says it instead.
            Core stated = statedAt(inv.expr(), type, given);
            List<Clause> o = stated == null ? null
                    : obligations(stated, k, at, unnamed, true, decidesFalse);
            if (o != null) {
                owed.addAll(o);
            }
        }
        if (owed.isEmpty()) {
            return Verdict.PROVED;   // nothing here is expressible — the run-time check stands for it
        }
        NumericDomain dom = k.numbers();
        for (Clause c : owed) {
            for (Constraint known : c.known()) {
                dom = dom.assume(known.form(), known.rel());
            }
        }
        Verdict out = Verdict.PROVED;
        for (Clause c : owed) {
            if (c.dischargedBy(dom, k.facts())) {
                continue;
            }
            if (c.refutedBy(dom, k.facts())) {
                return Verdict.REFUTED;
            }
            out = Verdict.UNKNOWN;
        }
        return out;
    }

    /** Whether the constant check reads this construction: a newtype's, over a value written where
     * it is built. That check names the clause that failed, so it is left to say it — and it reads
     * the construction as written, so a name given the value is not one it sees. */
    private static boolean constantlyBuilt(Ast.Data type, Core.NewData nd) {
        return type.newtype() && nd.inits().size() == 1 && isWritten(nd.inits().get(0).value());
    }

    /** Says what {@code verdict} found. A definite violation is an error and an unproven one a
     * warning; a discharged or non-expressible invariant says nothing. An {@code attempted}
     * construction raises no warning: what the warning reports is a possible abort, and an attempt
     * takes its else branch instead. */
    private void report(Core at, Ast.Data type, SourcePos pos, boolean attempted, Verdict verdict) {
        if (capturing != null) {
            capturing.found().put(new Occurrence(asWritten(at)),
                    new Reported(type, pos, verdict, attempted));
            return;
        }
        switch (verdict) {
            case REFUTED -> reportViolation(type, pos);
            case UNKNOWN -> {
                if (!attempted) {
                    warnings.add(Diagnostic.of("E2011", "check.invariant.unproven")
                            .title("check.invariant.title").at(pos).args(type.name())
                            .hint("check.invariant.reify", type.name()).warning().build());
                }
            }
            case PROVED -> { }
        }
    }

    /** What a construction came out as where it is being read on a branch rather than said. */
    private record Reported(Ast.Data type, SourcePos pos, Verdict verdict, boolean attempted) {}

    /**
     * Which construction a reading found: the one in the body as it was written. A reading is that
     * body with a conditional replaced, so the constructions along the way to the replacement are
     * rebuilt — those are the same construction given a different value, and they answer together.
     * One written inside the replacement is only in the reading that reached it, and one beside it
     * is the very node, unchanged.
     */
    private record Occurrence(Core of) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Occurrence x && x.of == of;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(of);
        }
    }

    /** What each node a rewrite built stands for, so a construction keeps its identity through one. */
    private final Map<Core, Core> rebuilt = new IdentityHashMap<>();

    /** The node {@code e} was built from, however many rewrites ago. */
    private Core asWritten(Core e) {
        Core from = e;
        Core next;
        while ((next = rebuilt.get(from)) != null) {
            from = next;
        }
        return from;
    }

    /**
     * Where a walk is reading one branch, what it finds is collected here rather than said. A body
     * read on each branch of a conditional reads every construction after it once per branch, and one
     * construction is one answer: it is the branches together that decide, the same as for a
     * construction the conditional is written inside.
     */
    private Capture capturing;

    /** What each declaration's fields are. Asked at every field read the walk goes past, and building
     * one walks the declaration's includes, so it is built once per declaration instead. */
    private final Map<Ast.Data, Map<String, Type>> fieldsOf = new HashMap<>();

    /** The same, for the binding each field is. */
    private final Map<Ast.Data, Map<String, BindingId>> fieldBindings = new HashMap<>();

    /** Each clause as the checker typed it, over the fields it is written against. */
    private final Map<Ast.Expr, Optional<Core>> typedClauses = new IdentityHashMap<>();

    /** What a reading has found so far. */
    private record Capture(Map<Occurrence, Reported> found) {

        static Capture empty() {
            return new Capture(new LinkedHashMap<>());
        }
    }

    /** What reading {@code e} finds, or nothing where the conditions along the way contradict — a
     * branch nothing reaches finds nothing, and what is not there violates nothing. */
    private Map<Occurrence, Reported> reading(Core e, Known k, Denotations at, int depth) {
        if (k.numbers().isBottom()) {
            return Map.of();
        }
        Capture outer = capturing;
        Capture mine = Capture.empty();
        capturing = mine;
        try {
            walk(e, k, at, depth + 1);
        } finally {
            capturing = outer;
        }
        return mine.found();
    }

    /**
     * The first conditional {@code e} gives a value to, or {@code null} where it gives none. A
     * conditional in tail position — an {@code if}'s own branches, a {@code let}'s body, a case's
     * body — is where the walk goes next rather than a value it is handed, and a closure's body is
     * read where the closure is applied.
     */
    private static Core.If conditionalValueIn(Core e) {
        return switch (e) {
            // Where the walk goes next is not a value it is handed: an `if`'s own branches, a `let`'s
            // body and a case's body are read after this, each with what is known there.
            case Core.If iff -> conditionalIn(iff.cond());
            case Core.IfConstructed ic -> conditionalIn(ic.construct());
            case Core.LetIn li -> conditionalIn(li.value());
            case Core.Match m -> conditionalIn(m.scrutinee());
            default -> conditionalIn(e);
        };
    }

    /** The first conditional inside a value. Everything under one is part of it, including the body
     * of a binding an expansion introduced — {@code let $0 = r in if $0.a > b then ...} is a helper
     * called on an argument, which is one value however many bindings writing it took. */
    private static Core.If conditionalIn(Core e) {
        if (e instanceof Core.If iff) {
            return iff;
        }
        if (e instanceof Core.Block) {
            return null;   // read where the closure is applied
        }
        Core.If[] found = {null};
        Core.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = conditionalIn(child);
            }
        });
        return found[0];
    }

    /**
     * {@code e} with every occurrence of {@code was} replaced by {@code becomes}. Occurrence is by
     * what it computes and not by where it is written: an author who writes one conditional twice —
     * once to guard on and once to build from — wrote one value, and reading the two as two would
     * make the guard say nothing about what is built.
     */
    private Core without(Core e, Core.If was, String key, Core becomes, Denotations at) {
        if (e == was || (key != null && e instanceof Core.If && key.equals(bodyKey(e, at)))) {
            return becomes;
        }
        if (e instanceof Core.Block) {
            return e;
        }
        Core made = Core.mapChildren(e, child -> without(child, was, key, becomes, at),
                name -> name,
                nd -> (Core.NewData) Core.mapChildren(nd,
                        child -> without(child, was, key, becomes, at), name -> name));
        if (made != e) {
            rebuilt.put(made, e);
        }
        return made;
    }

    /** Says of each construction the two readings reached what the two of them together decide. One
     * that only one reading reached is discharged on the other: it is not there to violate anything. */
    private void say(Map<Occurrence, Reported> a, Map<Occurrence, Reported> b) {
        Set<Occurrence> at = new LinkedHashSet<>(a.keySet());
        at.addAll(b.keySet());
        for (Occurrence one : at) {
            Reported x = a.get(one);
            Reported y = b.get(one);
            if (x == null || y == null) {
                // Written inside one branch, so the other reading did not discharge it — it was not
                // there to discharge. What the reading that reached it found is what it is.
                Reported said = x != null ? x : y;
                report(one.of(), said.type(), said.pos(), said.attempted(), said.verdict());
                continue;
            }
            report(one.of(), x.type(), x.pos(), x.attempted(),
                    Verdict.of(x.verdict(), y.verdict()));
        }
    }

    private void reportViolation(Ast.Data type, SourcePos pos) {
        errors.add(CompileException.of(
                Diagnostic.of("E2010", "check.invariant.violation").title("check.invariant.title")
                        .at(pos).args(type.name()).build(),
                "constructing `" + type.name() + "` here violates its invariant on a reachable path"));
    }

    // --- a clause, read where a value is built -------------------------------------------------

    /**
     * {@code clause} as the checker types it: over the declaration's own fields, each a binding, in
     * the representation this check reads. Asked once per clause, because typing one walks it.
     *
     * <p>Null where the clause is not one this compiler could type there. That is the same answer as
     * a clause naming something outside the fragment — the run-time check stands for it — and it is
     * an answer rather than a failure because a declaration this check cannot read is not a
     * declaration an author wrote wrongly.
     */
    private Core typed(Ast.Expr clause, Ast.Data data) {
        return typedClauses.computeIfAbsent(clause, written -> {
            try {
                return Optional.ofNullable(Elaborator.elaborate(written, fieldScope(data),
                        CheckContext.of(symbols).forData(data)
                                .preserving(Preserved.byTheLanguagesOwnOperations()),
                        Type.BOOL));
            } catch (RuntimeException _) {
                return Optional.empty();
            }
        }).orElse(null);
    }

    /** The bindings a declaration's own invariant reads: its fields, each as the binding it is. */
    private Scope fieldScope(Ast.Data data) {
        return DataChecker.fieldScope(data, symbols);
    }

    /**
     * What a clause of {@code data} states where each field is given what {@code given} says, or
     * {@code null} where it states nothing this check can read.
     *
     * <p>The clause is the declaration's and the values are the site's, and this is where the two
     * become one expression: a field read stands for the value that field is being given, so what the
     * clause says is read by the very rules the body is read by. A field nothing was given — one a
     * construction leaves out — leaves the clause naming a value that is not there, and the clause is
     * left to the run-time check rather than read against nothing.
     */
    private Core statedAt(Ast.Expr clause, Ast.Data data, Map<BindingId, Core> given) {
        Core typed = typed(clause, data);
        if (typed == null) {
            return null;
        }
        Set<BindingId> fields = new HashSet<>(fieldBindingsOf(data).values());
        boolean[] whole = {true};
        readsOf(typed, binding -> {
            if (fields.contains(binding) && !given.containsKey(binding)) {
                whole[0] = false;
            }
        });
        return whole[0] ? substituted(typed, given) : null;
    }

    /** {@code e} with each binding {@code given} names replaced by the value it was given. */
    private static Core substituted(Core e, Map<BindingId, Core> given) {
        if (e instanceof Core.Read r) {
            Core value = given.get(r.binding());
            return value != null ? value : r;
        }
        return Core.mapChildren(e, child -> substituted(child, given),
                // A name slot holds a binding and nothing else, so a value put there would be
                // something the reader of that slot cannot load. Only another name may stand there.
                name -> substituted(name, given) instanceof Core.Read r ? r : name,
                nd -> (Core.NewData) Core.mapChildren(nd, child -> substituted(child, given),
                        name -> substituted(name, given) instanceof Core.Read r ? r : name));
    }

    /** Every binding {@code e} reads, at any depth. */
    private static void readsOf(Core e, java.util.function.Consumer<BindingId> f) {
        if (e instanceof Core.Read r) {
            f.accept(r.binding());
        }
        Core.forEachChild(e, child -> readsOf(child, f));
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

    /** A clause that cannot hold, said in the language the domain reads: {@code -1 >= 0}. */
    private static final Clause VIOLATED = new Clause(
            new Constraint(LinearForm.constant(BigDecimal.ONE.negate()), Rel.GE), null, List.of());

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

    /** What {@code inv} owes, where {@code decidesFalse} says a clause folding to the other answer
     * than it is read with is this check's to report. A newtype's constant construction is checked
     * elsewhere, and that check names the clause that failed rather than only saying one did, so it
     * is left to say it. */
    private List<Clause> obligations(Core inv, Known k, Denotations at, boolean decidesFalse) {
        return obligations(inv, k, at, Set.of(), true, decidesFalse);
    }

    private List<Clause> obligations(Core rawInv, Known k, Denotations at, Set<Core> unnamed,
                                     boolean positive, boolean decidesFalse) {
        Core inv = asSizeComparison(rawInv);
        if (inv instanceof Core.Binary b && b.op() == Ast.BinOp.AND && positive) {
            // Each conjunct on its own: an invariant is a set of things that hold, and one the check
            // cannot read leaves its own run-time check standing without costing the others theirs.
            List<Clause> l = obligations(b.left(), k, at, unnamed, true, decidesFalse);
            List<Clause> r = obligations(b.right(), k, at, unnamed, true, decidesFalse);
            if (l == null && r == null) {
                return null;
            }
            List<Clause> both = new ArrayList<>(l == null ? List.of() : l);
            both.addAll(r == null ? List.of() : r);
            return both;
        }
        Core under = negated(inv);
        if (under != null) {
            return obligations(under, k, at, unnamed, !positive, decidesFalse);
        }
        Boolean folded = decidedAt(inv);
        if (folded != null) {
            // The clause folds once the construction's own expressions stand where it read a field.
            // Folding the way it is read owes nothing; folding the other way is a violation, and
            // saying so needs no term to be named. Read under a denial it is the other answer that
            // discharges, which is why the polarity is asked.
            if (folded == positive) {
                return List.of();
            }
            if (decidesFalse) {
                return List.of(VIOLATED);
            }
        }
        Constraint numeric = null;
        if (inv instanceof Core.Binary b && relOf(b.op()) != null) {
            Rel eff = positive ? relOf(b.op()) : negateRel(relOf(b.op()));
            LinearForm la = eff == null ? null : affineOf(b.left(), at, k);
            LinearForm ra = eff == null ? null : affineOf(b.right(), at, k);
            if (la != null && ra != null) {
                numeric = new Constraint(la.minus(ra), eff);
            }
        }
        Polar polar = polar(inv, positive);
        // A predicate over a value no guard could be written about is not a predicate a guard will
        // settle, so it is not owed as one — where the domain can say something of that value it has
        // already said it above, and where it cannot the run-time check stands for the clause.
        List<String> keys = names(polar.expr(), unnamed) ? List.of() : factKeys(polar.expr(), at);
        boolean stated = polar.positive();
        Fact fact = keys.isEmpty() ? null : new Fact(stated ? keys : firstOnly(keys), stated);
        if (numeric == null && fact == null) {
            return null;
        }
        List<Constraint> known = new ArrayList<>();
        sizeFacts(inv, at, known);
        return List.of(new Clause(numeric, fact, known));
    }

    /** Whether {@code inv} is decided outright: the clause, with the construction's own values
     * already standing where it read a field, folded. {@code null} where it does not fold — which is
     * every clause reading anything computed at run time. */
    private Boolean decidedAt(Core inv) {
        Object folded = folded(inv);
        return folded instanceof Boolean b ? b : null;
    }

    /** What {@code e} folds to where every part of it is written out, or {@code null} where any part
     * of it is computed at run time and there is nothing to fold. */
    private static Object folded(Core e) {
        Ast.Expr written = asWrittenValue(e);
        return written == null ? null : ConstEval.eval(written).orElse(null);
    }

    private static List<String> firstOnly(List<String> keys) {
        return keys.isEmpty() ? keys : List.of(keys.get(0));
    }

    /** Refines {@code k} by asserting {@code cond} (or its negation): a comparison tightens the
     * numeric domain, a stdlib predicate settles a fact. A condition of neither shape, and an operand
     * outside the affine fragment, leave {@code k} unchanged (sound). */
    private Known assumeCond(Core rawCond, Known k, Denotations at, boolean positive) {
        Core cond = asSizeComparison(rawCond);
        // `&&` asserted true gives both sides; `||` asserted false gives both sides negated.
        if (cond instanceof Core.Binary b
                && (b.op() == Ast.BinOp.AND && positive || b.op() == Ast.BinOp.OR && !positive)) {
            return assumeCond(b.right(), assumeCond(b.left(), k, at, positive), at, positive);
        }
        Core under = negated(cond);
        if (under != null) {
            return assumeCond(under, k, at, !positive);
        }
        Known out = k;
        // What holds of the sizes the condition names, whichever way the condition itself is read.
        List<Constraint> known = new ArrayList<>();
        sizeFacts(cond, at, known);
        for (Constraint c : known) {
            out = out.with(out.numbers().assume(c.form(), c.rel()));
        }
        if (cond instanceof Core.Binary b) {
            Rel rel = relOf(b.op());
            Rel eff = rel == null ? null : positive ? rel : negateRel(rel);
            LinearForm la = eff == null ? null : affineOf(b.left(), at, out);
            LinearForm ra = eff == null ? null : affineOf(b.right(), at, out);
            if (la != null && ra != null) {
                out = out.with(out.numbers().assume(la.minus(ra), eff));
            }
            // What the comparison named, recorded as spoken about: a construction from one of these
            // is one the author has said something about, whichever route ends up carrying it.
            Set<String> named = new HashSet<>(spokenOf(b.left(), at, la));
            named.addAll(spokenOf(b.right(), at, ra));
            out = out.speaking(named);
        }
        List<Quantified> quantified = new ArrayList<>();
        quantifiedBy(cond, at, positive, quantified);
        out = out.and(quantified);
        // Both routes, always: which one carries a clause is decided where the clause is read, and a
        // guard does not know which that will be.
        Polar polar = polar(cond, positive);
        String key = bodyKey(polar.expr(), at);
        return key == null ? out : out.with(out.facts().assume(key, polar.positive()));
    }

    /** The terms one side of a compared pair names: the expression itself, and each atom of the form it
     * reduced to — {@code leftover + 1} says something about {@code leftover}. */
    private Collection<String> spokenOf(Core side, Denotations at, LinearForm form) {
        Set<String> terms = new HashSet<>(form == null ? Set.of() : form.coefs().keySet());
        String written = bodyKey(side, at);
        if (written != null) {
            terms.add(written);
        }
        return terms;
    }

    /** A predicate as one of {@code ==}/{@code <} states it, and whether it is being stated or denied. */
    private record Polar(Core expr, boolean positive) {}

    /**
     * {@code e}, asserted with polarity {@code positive}, as the comparison of {@code ==} or {@code <}
     * that says the same thing: {@code a /= b} is {@code a == b} denied, {@code a >= b} is
     * {@code a < b} denied, and {@code a > b} is {@code b < a}. A fact is settled by key equality, so
     * without this the six ways to compare two terms are six facts, and a guard written one way would
     * leave a clause written the other unsettled.
     */
    private static Polar polar(Core e, boolean positive) {
        if (!(e instanceof Core.Binary b) || relOf(b.op()) == null) {
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

    private static Core.Binary comparison(Ast.BinOp op, Core left, Core right, Core.Binary of) {
        return new Core.Binary(op, left, right, of.type(), of.pos());
    }

    /** What a negation is applied to, or {@code null} if {@code e} is not one. {@code Bool.not} is an
     * ordinary helper: the analysis representation keeps it as a call, and a clause read off an
     * imported declaration is the body it expands to — {@code if b then false else true} over a
     * binding holding the argument. Both are read. */
    private static Core negated(Core e) {
        if (e instanceof Core.PreservedCall call && call.operation().equals(op("Bool.not"))
                && call.args().size() == 1) {
            return call.args().get(0);
        }
        if (e instanceof Core.LetIn li) {
            Core inner = negated(li.body());
            return inner instanceof Core.Read r && r.binding().equals(li.binder().id())
                    ? li.value() : null;
        }
        return e instanceof Core.If iff
                && iff.then() instanceof Core.Bool t && !t.value()
                && iff.els() instanceof Core.Bool f && f.value()
                ? iff.cond() : null;
    }

    // --- seeding -------------------------------------------------------------------------------

    /**
     * Seeds the check with what the type of the value at {@code root} guarantees: a numeric newtype's
     * own invariant on its value, a predicate its invariant states of it, or a product data's
     * invariant over its fields (and one level of fields), each read at that very value. Sound by
     * closed construction — a value of type T was built through T's checked constructor.
     *
     * <p>Which is the same reading a construction gets, over field reads instead of field values: the
     * clause is the declaration's either way, and where it is established and where it is owed differ
     * only in direction.
     */
    private Known seedAt(Core root, Known k, Denotations at, int depth) {
        if (depth > 2 || !(root.type() instanceof Type.Ref ref)
                || !(symbols.get(ref.name()) instanceof Ast.Data data)) {
            return k;
        }
        Map<String, Type> fields = fieldsOf(data);
        Map<String, BindingId> bindings = fieldBindingsOf(data);
        Map<BindingId, Core> given = new HashMap<>();
        fields.forEach((name, type) -> {
            BindingId field = bindings.get(name);
            if (field != null) {
                given.put(field, new Core.FieldAccess(root, name, type, root.pos()));
            }
        });
        Known out = k;
        List<Quantified> quantified = new ArrayList<>();
        for (Ast.InvariantClause inv : invariantsOf(ref.name(), data)) {
            Core stated = statedAt(inv.expr(), data, given);
            if (stated == null) {
                continue;
            }
            quantifiedBy(stated, at, true, quantified);
            out = assume(obligations(stated, out, at, false), out);
        }
        out = out.and(quantified);
        if (data.newtype()) {
            // A newtype's `.value` is the same location as the newtype, so what its base guarantees is
            // guaranteed of this very atom: `data Outer = Inner` carries Inner's invariant.
            Core value = given.get(bindings.get("value"));
            return value == null ? out : seedAt(value, out, at, depth + 1);
        }
        for (Core value : given.values()) {
            out = seedAt(value, out, at, depth + 1);
        }
        return out;
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

    // --- affine forms --------------------------------------------------------------------------

    /** The operator {@code e} is, where it is a library call written as a function, or {@code e}
     * itself. Reading it as the operator is what puts it on the one path the operator already has,
     * rather than on a second path that would have to be kept saying the same thing. */
    private static Core asOperator(Core e) {
        if (e instanceof Core.PreservedCall call && call.args().size() == 2) {
            Ast.BinOp op = OPERATOR_CALLS.get(call.operation());
            if (op != null) {
                return new Core.Binary(op, call.args().get(0), call.args().get(1), call.type(),
                        call.pos());
            }
        }
        return e;
    }

    /** The shared affine walk: literals and {@code +}/{@code -} compose; every other node is handed to
     * {@code leaf} (which decides whether it is an atom, a location, or opaque). */
    private LinearForm affine(Core raw, java.util.function.Function<Core, LinearForm> leaf) {
        Core e = asOperator(raw);
        if (e instanceof Core.PreservedCall) {
            // A call that folds is the number it folds to. `String.length("1A")` is 2, and a clause
            // about it is decided rather than owed — the run-time check is not what should answer a
            // question the compiler has already computed. Asked once: folding walks the subtree, and
            // a pattern in it is a regex to run.
            BigDecimal folded = constantNumber(e);
            if (folded != null) {
                return LinearForm.constant(folded);
            }
        }
        return switch (e) {
            case Core.Int i -> LinearForm.constant(BigDecimal.valueOf(i.value()));
            case Core.Decimal d -> LinearForm.constant(d.value());
            case Core.Neg n -> negate(affine(n.operand(), leaf));
            case Core.Binary b when b.op() == Ast.BinOp.ADD ->
                    add(affine(b.left(), leaf), affine(b.right(), leaf), false);
            case Core.Binary b when b.op() == Ast.BinOp.SUB ->
                    add(affine(b.left(), leaf), affine(b.right(), leaf), true);
            // scalar multiply by a constant (Amount * 2) is linear; `/` and a variable product are not
            // (a divide truncates for Int, and a variable factor is non-linear), so leave those opaque.
            case Core.Binary b when b.op() == Ast.BinOp.MUL ->
                    scale(affine(b.left(), leaf), affine(b.right(), leaf));
            // A binding an expansion introduced (`let $0_n = n.value in $0_n * 2`) is what an
            // arithmetic helper becomes, so reading through it is reading the arithmetic the author
            // wrote.
            case Core.LetIn li -> {
                LinearForm bound = affine(li.value(), leaf);
                yield bound == null ? leaf.apply(e) : affine(li.body(),
                        n -> n instanceof Core.Read r && r.binding().equals(li.binder().id())
                                ? bound : leaf.apply(n));
            }
            default -> leaf.apply(e);
        };
    }

    /** The number {@code e} folds to at compile time, or {@code null} where it folds to none. */
    private static BigDecimal constantNumber(Core e) {
        Object folded = folded(e);
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

    /** The affine form of an expression: a numeric atom, a newtype construct's wrapped value, or
     * {@code null}. */
    private LinearForm affineOf(Core e, Denotations at, Known k) {
        return affine(e, n -> {
            if (n instanceof Core.NewData nd && nd.spreads().isEmpty() && nd.inits().size() == 1
                    && nd.inits().get(0).name().equals("value")
                    && numericNewtype(Type.ref(nd.typeName()))) {
                return affineOf(nd.inits().get(0).value(), at, k);
            }
            Core written = writtenValue(n, at);
            if (written != null && written != n) {
                return affineOf(written, at, k);
            }
            // A list written out has as many elements as it is written with, whatever they are.
            BigDecimal counted = writtenSize(n, at);
            if (counted != null) {
                return LinearForm.constant(counted);
            }
            String atom = atomOf(n, at, k);
            return atom == null ? null : LinearForm.atom(atom);
        });
    }

    /** How many elements a size call over a value written out counts, or {@code null} where its
     * argument is not one. */
    private BigDecimal writtenSize(Core e, Denotations at) {
        if (!(e instanceof Core.PreservedCall call) || !SIZE_CALLS.contains(call.operation())
                || call.args().size() != 1) {
            return null;
        }
        Core written = writtenValue(call.args().get(0), at);
        return written instanceof Core.ListLit list
                ? BigDecimal.valueOf(list.elements().size()) : null;
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
    private String atomOf(Core e, Denotations at, Known k) {
        String size = sizeAtom(e, arg -> bodyKey(arg, at));
        if (size != null) {
            return size;
        }
        if (!isNumeric(e.type())) {
            return null;
        }
        // A path rooted at a binding is the atom of what that binding denotes, and only where a clause
        // could be read against it — otherwise a name would be an atom where the expression it was
        // given is not one, and the two spellings would answer differently.
        BindingId root = rootBinding(e);
        if (root != null && !readable(at.of(root), k)) {
            return null;
        }
        return pathKey(e, at);
    }

    /** An expression's canonical key: a location names itself, and everything else is read
     * structurally. */
    private String bodyKey(Core e, Denotations at) {
        return termKey(e, at, Map.of(), 0);
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
    private String siteKey(Core e, Denotations at, Known k) {
        // A value written out is not something a guard can be written about: there is nothing to
        // state of `"xyz"` that the text does not already say. Where a clause reading it folds it is
        // decided before this is asked, and where it does not fold there is no guard that would
        // discharge it, so naming it here would only report what the author cannot answer.
        Denotes d = denotationOf(e, at, k);
        return readable(d, k) ? d.key() : null;
    }

    /** The atom key of {@code SIZE_CALL(container)} when {@code key} can name the container, else
     * {@code null}. */
    private static String sizeAtom(Core e, java.util.function.Function<Core, String> key) {
        if (!(e instanceof Core.PreservedCall call) || !SIZE_CALLS.contains(call.operation())
                || call.args().size() != 1) {
            return null;
        }
        String arg = key.apply(sizeSource(call.args().get(0)));
        return arg == null ? null : call.operation().name() + "(" + arg + ")";
    }

    /** The container a size is really the size of: an operation that keeps the size of what it was
     * built from is peeled away, so {@code List.length(List.map(f, xs))} is the atom
     * {@code List.length(xs)}. How the elements are made has no bearing on how many there are, which
     * is why the closure does not enter the key. */
    private static Core sizeSource(Core e) {
        if (e instanceof Core.PreservedCall call) {
            Built built = BUILT_FROM.get(call.operation());
            if (built != null && built.shape().keepsSize() && built.from() < call.args().size()) {
                return sizeSource(call.args().get(built.from()));
            }
        }
        return e;
    }

    /** What is known of the size of every container an expression names: never negative, and no
     * greater than the size of what it was built from wherever the building can only drop elements. */
    private void sizeFacts(Core e, Denotations at, List<Constraint> out) {
        // A name is what it was given, here as everywhere: what is known of a size does not depend on
        // whether the size was written where it is read or bound first.
        if (e instanceof Core.Read r && at.valueOf(r.binding()) != null) {
            sizeFacts(at.valueOf(r.binding()), at, out);
            return;
        }
        if (!(e instanceof Core.PreservedCall call)) {
            Core.forEachChild(e, child -> sizeFacts(child, at, out));
            return;
        }
        if (SIZE_CALLS.contains(call.operation()) && call.args().size() == 1) {
            String atom = sizeAtom(call, arg -> bodyKey(arg, at));
            if (atom != null) {
                out.add(new Constraint(LinearForm.atom(atom), Rel.GE));   // a size is never negative
                bounds(call.operation(), sizeSource(call.args().get(0)), at, out);
            }
        }
        for (Core arg : call.args()) {
            sizeFacts(arg, at, out);
        }
    }

    /** {@code size(c) <= size(what c was built from)}, down the chain, wherever the building can only
     * drop elements. */
    private void bounds(ValueName sizeCall, Core container, Denotations at, List<Constraint> out) {
        if (!(container instanceof Core.PreservedCall call)) {
            return;
        }
        Built built = BUILT_FROM.get(call.operation());
        if (built == null || built.shape().keepsSize() || built.from() >= call.args().size()) {
            return;
        }
        Core source = sizeSource(call.args().get(built.from()));
        String here = bodyKey(container, at);
        String there = bodyKey(source, at);
        if (here == null || there == null) {
            return;
        }
        out.add(new Constraint(
                LinearForm.atom(sizeCall.name() + "(" + here + ")")
                        .minus(LinearForm.atom(sizeCall.name() + "(" + there + ")")),
                Rel.LE));
        bounds(sizeCall, source, at, out);
    }

    /** The keys a guard could have settled to establish this clause: the predicate as written, and
     * the same predicate of each container the written one was built from by a construction that
     * carries it. Stating {@code List.all(p, xs)} is stating it of every sublist of {@code xs}. */
    private List<String> factKeys(Core inv, Denotations at) {
        String written = bodyKey(inv, at);
        if (written == null) {
            return List.of();
        }
        List<String> keys = new ArrayList<>();
        keys.add(written);
        if (!(inv instanceof Core.PreservedCall call)) {
            return keys;
        }
        Carried carried = CARRIED.get(call.operation());
        if (carried == null || carried.container() >= call.args().size()) {
            return keys;
        }
        // The predicate over each container the one it names was built from. The container is the
        // construction's own expression, so the operations peeled off are the ones the body wrote.
        Core container = call.args().get(carried.container());
        Core.PreservedCall stated = call;
        while (container instanceof Core.PreservedCall inner) {
            Built built = BUILT_FROM.get(inner.operation());
            if (built == null || built.from() >= inner.args().size()) {
                break;
            }
            Core.PreservedCall next = carries(stated, carried, inner, built, at);
            if (next == null) {
                break;
            }
            Core source = inner.args().get(built.from());
            String key = bodyKey(withArg(next, carried.container(), source), at);
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
    private Core.PreservedCall carries(Core.PreservedCall stated, Carried carried,
                                       Core.PreservedCall inner, Built built, Denotations at) {
        if (carried.through().contains(built.shape())) {
            return stated;
        }
        Integer projection = PROJECTION_OF.get(stated.operation());
        if (built.shape() != Shape.MAPS || projection == null
                || projection >= stated.args().size()) {
            return null;
        }
        // Where the mapping's closure is written is already stated once, by the table that says which
        // argument each combinator hands its elements to.
        Combinator combo = COMBINATORS.get(inner.operation());
        if (combo == null || combo.closureArg() >= inner.args().size()) {
            return null;
        }
        Core traced = projectionThrough(stated.args().get(projection),
                inner.args().get(combo.closureArg()), at);
        return traced == null ? null : withArg(stated, projection, traced);
    }

    /**
     * The projection over an element that a projection over a mapped list reduces to, or
     * {@code null}.
     *
     * <p>{@code .product} over {@code List.map(r -> Line { product = r.product, ... }, xs)} is
     * {@code .product} over {@code xs}: the closure copied that field across, so two mapped elements
     * differ there exactly when the two they came from did. Bounded deliberately — a field a closure
     * computes from others is not this.
     *
     * <p>What comes back is a projection to be keyed and nothing else. A block keys its parameter by
     * where it is bound, so the chain built here is read at the position the closure's parameter
     * stands in, whatever it is called and whatever it was read from.
     */
    private Core projectionThrough(Core projection, Core closure, Denotations at) {
        Core.Block proj = blockOf(projection, at);
        Core.Block step = blockOf(closure, at);
        if (proj == null || proj.params().size() != 1 || step == null
                || step.params().size() != 1) {
            return null;
        }
        Ast.Binder element = step.params().get(0);
        List<String> read = new Reads(proj.params().get(0).id()).chain(proj.body());
        if (read == null) {
            return null;
        }
        Reads reads = new Reads(element.id());
        Core made = reads.produced(step.body());
        List<String> traced;
        if (read.isEmpty()) {
            traced = reads.chain(made);   // the closure hands the element straight back
        } else {
            if (!(made instanceof Core.NewData nd) || !nd.spreads().isEmpty()) {
                return null;
            }
            List<String> copied = null;
            for (Core.FieldInit fi : nd.inits()) {
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
        Core on = read(element, elementType(step.type()), step.pos());
        for (String field : traced) {
            on = new Core.FieldAccess(on, field, fieldType(on.type(), field), step.pos());
        }
        return new Core.Block(List.of(element), on, step.type(), step.pos());
    }

    /**
     * What the names in a closure read off the element it is handed: a field chain, or nothing this
     * trace can follow. A binding introduces what it reads <em>where it is written</em> — an expansion
     * splices {@code let $0_r = r in ...} into a closure — so what a name denotes is settled against
     * the bindings before it and not reread later.
     */
    private static final class Reads {

        private final BindingId element;
        private final Map<BindingId, List<String>> chains = new HashMap<>();

        private Reads(BindingId element) {
            this.element = element;
        }

        /** The expression the body produces, with what the bindings on the way there read taken in. */
        Core produced(Core body) {
            Core cur = body;
            while (cur instanceof Core.LetIn li) {
                chains.put(li.binder().id(), chain(li.value()));
                cur = li.body();
            }
            return cur;
        }

        /** The chain {@code e} reads off the element, or {@code null} if it reads anything else. */
        List<String> chain(Core e) {
            return switch (e) {
                case Core.LetIn li -> {
                    Reads inner = new Reads(element);
                    inner.chains.putAll(chains);
                    inner.chains.put(li.binder().id(), chain(li.value()));
                    yield inner.chain(li.body());
                }
                case Core.FieldAccess fa -> {
                    List<String> head = chain(fa.target());
                    if (head == null) {
                        yield null;
                    }
                    List<String> out = new ArrayList<>(head);
                    out.add(fa.field());
                    yield out;
                }
                case Core.Read r when chains.containsKey(r.binding()) -> chains.get(r.binding());
                case Core.Read r -> r.binding().equals(element) ? List.of() : null;
                default -> null;
            };
        }
    }

    private static Core.PreservedCall withArg(Core.PreservedCall call, int at, Core arg) {
        List<Core> args = new ArrayList<>(call.args());
        args.set(at, arg);
        return new Core.PreservedCall(call.operation(), args, call.type(), call.pos());
    }

    /** An emptiness check as the comparison it means, or {@code e} unchanged. */
    private static Core asSizeComparison(Core e) {
        if (e instanceof Core.PreservedCall call && call.args().size() == 1
                && EMPTINESS.containsKey(call.operation())) {
            Core size = new Core.PreservedCall(EMPTINESS.get(call.operation()), call.args(),
                    Type.INT, call.pos());
            return new Core.Binary(Ast.BinOp.EQ, size, new Core.Int(0, Type.INT, call.pos()),
                    Type.BOOL, call.pos());
        }
        return e;
    }

    /**
     * The canonical key of an expression as a term, or {@code null} when nothing here can be named.
     * Two expressions with one key compute one value, which is the whole of what the fact set knows:
     * a guard and an invariant clause state the same predicate exactly when their calls key alike.
     *
     * <p>A location keys as the location it is, so which value a term is about is the binding it is
     * rooted at. A closure parameter is keyed by where it is bound rather than by its binding, so
     * {@code r -> r.a} and {@code row -> row.a} are one term while a free name inside the closure is
     * still the value it is and so is part of the term. Anything outside this grammar keys as
     * {@code null}, and the clause reading it is left opaque.
     */
    private String termKey(Core raw, Denotations at, Map<BindingId, String> bound, int depth) {
        Core e = asOperator(raw);
        BindingId root = rootBinding(e);
        if (root != null) {
            String here = bound.get(root);
            return here != null ? chainOn(here, e) : pathKey(e, at);
        }
        return switch (e) {
            case Core.Int i -> Long.toString(i.value());
            case Core.Decimal d -> d.value().toPlainString() + "m";
            case Core.Str s -> quoted(s.value());
            case Core.Bool b -> Boolean.toString(b.value());
            case Core.UnitValue u -> u.data().toString();
            case Core.Neg n -> wrap("-", termKey(n.operand(), at, bound, depth));
            case Core.Binary b -> {
                String l = termKey(b.left(), at, bound, depth);
                String r = termKey(b.right(), at, bound, depth);
                yield l == null || r == null ? null : binaryKey(b.op(), l, r);
            }
            case Core.ListLit l -> elementsKey("[", l.elements(), at, bound, depth, "]");
            case Core.Tuple t -> elementsKey("(", t.elements(), at, bound, depth, ")");
            case Core.TupleGet g -> wrap("." + g.index(), termKey(g.tuple(), at, bound, depth));
            case Core.If iff -> elementsKey("if(", List.of(iff.cond(), iff.then(), iff.els()),
                    at, bound, depth, ")");
            case Core.Block b -> {
                Map<BindingId, String> inner = binding(bound, b.params(), depth);
                yield wrap("\\" + b.params().size(), termKey(b.body(), at, inner, depth + 1));
            }
            case Core.LetIn li -> {
                String value = termKey(li.value(), at, bound, depth);
                Map<BindingId, String> inner = binding(bound, List.of(li.binder()), depth);
                String body = termKey(li.body(), at, inner, depth + 1);
                yield value == null || body == null ? null : "let(" + value + ", " + body + ")";
            }
            // A construction is a pure function of its fields, and a closure that builds one is what a
            // mapping usually is. Fields are keyed in name order, so two sites writing them in
            // different orders write one term.
            case Core.NewData nd when nd.spreads().isEmpty() -> {
                List<Core.FieldInit> inits = new ArrayList<>(nd.inits());
                inits.sort(java.util.Comparator.comparing(Core.FieldInit::name));
                StringBuilder sb = new StringBuilder(nd.typeName().toString()).append('{');
                for (int i = 0; i < inits.size(); i++) {
                    String v = termKey(inits.get(i).value(), at, bound, depth);
                    if (v == null) {
                        yield null;
                    }
                    sb.append(i == 0 ? "" : ", ").append(inits.get(i).name()).append('=').append(v);
                }
                yield sb.append('}').toString();
            }
            // Only the operations the representation kept standing: they are the library's own, so
            // they are pure and one written call is one value.
            case Core.PreservedCall c ->
                    elementsKey(c.operation().name() + "(", c.args(), at, bound, depth, ")");
            default -> null;
        };
    }

    /** {@code bound} with each of {@code binders} keyed by where it is bound rather than by which
     * binding it is, so two expressions that differ only in what they bound are one term. */
    private static Map<BindingId, String> binding(Map<BindingId, String> bound,
                                                  List<Ast.Binder> binders, int depth) {
        Map<BindingId, String> inner = new HashMap<>(bound);
        for (int i = 0; i < binders.size(); i++) {
            inner.put(binders.get(i).id(), "#" + depth + "." + i);
        }
        return inner;
    }

    private String elementsKey(String open, List<Core> parts, Denotations at,
                               Map<BindingId, String> bound, int depth, String close) {
        StringBuilder sb = new StringBuilder(open);
        for (int i = 0; i < parts.size(); i++) {
            String part = termKey(parts.get(i), at, bound, depth);
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

    /** The binding at the head of a {@code x}/{@code x.a.b} chain, or {@code null} if {@code e} is not
     * one. */
    private static BindingId rootBinding(Core e) {
        return switch (e) {
            case Core.Read r -> r.binding();
            case Core.FieldAccess fa -> rootBinding(fa.target());
            default -> null;
        };
    }

    /** The field chain of {@code e} rebuilt on {@code head}. */
    private static String chainOn(String head, Core e) {
        return e instanceof Core.FieldAccess fa ? chainOn(head, fa.target()) + "." + fa.field() : head;
    }

    /**
     * The key of a chain rooted at a binding: the location it is, or, where the binding was given a
     * term rather than a location, that term with the fields read from it.
     *
     * <p>A newtype's {@code .value} is the same location as the newtype, which is {@link Location}'s
     * rule and is read here of a term too, so a value keyed one way through a binding and the other
     * way through a field is one value.
     */
    private String pathKey(Core e, Denotations at) {
        Location located = locationOf(e, at);
        if (located != null) {
            return located.toString();
        }
        return switch (e) {
            case Core.Read r -> at.of(r.binding()).key();
            case Core.FieldAccess fa -> {
                if (!Location.isStep(fa.target().type(), fa.field(), symbols)) {
                    yield pathKey(fa.target(), at);
                }
                String base = pathKey(fa.target(), at);
                yield base == null ? null : base + "." + fa.field();
            }
            default -> null;
        };
    }

    /** The location {@code e} is, or {@code null} where it is a computed value rather than a place. */
    private Location locationOf(Core e, Denotations at) {
        return Location.of(e, symbols,
                binding -> at.of(binding) instanceof Denotes.At located ? located.where() : null);
    }

    /**
     * What a binding's initializer denotes: the location it is where it is one, else the term it
     * computes, else nothing. A name is an alias and never a value of its own — this is the one place
     * that decides it, so an expression answers the same whether it was written where it is used or
     * given a name first.
     */
    private Denotes denotationOf(Core e, Denotations at, Known k) {
        Core written = writtenValue(e, at);
        if (written != null) {
            return new Denotes.Written(bodyKey(written, at), written);
        }
        Location located = locationOf(e, at);
        if (located != null) {
            return new Denotes.At(located);
        }
        String term = bodyKey(e, at);
        if (term == null) {
            return new Denotes.Nothing();
        }
        // Readable where there is something to say of it: a form the numeric domain built, or a rule
        // about how it was made. This is asked of the expression, so a name for it answers the same.
        return new Denotes.Term(term, affineOf(e, at, k) != null || namedByRule(e, at));
    }

    /**
     * Whether a clause may be read against what {@code d} denotes. A location always may: the seeding
     * writes about locations. A computed term may where something can be said of it, or where a guard
     * on this path has said something. Nothing never may.
     *
     * <p>Every question of the form "is this value one a clause can be read against" asks this, and
     * asking it of a name gives the same answer as asking it of the expression the name was bound to.
     * That is what makes naming an expression not change what is known of it.
     */
    private static boolean readable(Denotes d, Known k) {
        return switch (d) {
            case Denotes.At _ -> true;
            case Denotes.Term term -> term.readable() || k.speaksOf(term.key());
            case Denotes.Written _, Denotes.Nothing _ -> false;
        };
    }

    /** What {@code e} is written as, where it is a written value or a name given one — and
     * {@code null} where it is computed from anything. */
    private static Core writtenValue(Core e, Denotations at) {
        if (e instanceof Core.Read r) {
            return at.of(r.binding()) instanceof Denotes.Written w ? w.value() : null;
        }
        return isWritten(e) ? e : null;
    }

    /**
     * Whether {@code e} is a value written out rather than computed from anything: a literal, and a
     * list or a construction whose every part is one. A table written into the source is this — every
     * row of it is there to read — and there is no guard an author could add about it, which is what
     * naming it at a construction site would ask for.
     */
    private static boolean isWritten(Core e) {
        return isWritten(e, Set.of());
    }

    /** The same, where {@code written} names the bindings an expansion introduced for values that
     * were themselves written. A helper called on written arguments is a written value: what it
     * expands to binds each argument and reads it back, which is the source's own text moved. */
    private static boolean isWritten(Core e, Set<BindingId> written) {
        return switch (e) {
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.UnitValue _ -> true;
            case Core.Neg n -> isWritten(n.operand(), written);
            case Core.Read r -> written.contains(r.binding());
            case Core.ListLit list -> list.elements().stream().allMatch(x -> isWritten(x, written));
            case Core.Tuple t -> t.elements().stream().allMatch(x -> isWritten(x, written));
            case Core.OptionSome s -> isWritten(s.value(), written);
            case Core.NewData nd -> nd.spreads().isEmpty()
                    && nd.inits().stream().allMatch(fi -> isWritten(fi.value(), written));
            case Core.LetIn li -> {
                if (!isWritten(li.value(), written)) {
                    yield false;
                }
                Set<BindingId> inner = new HashSet<>(written);
                inner.add(li.binder().id());
                yield isWritten(li.body(), inner);
            }
            default -> false;
        };
    }

    /** Whether {@code e} is a container built by an operation the preservation table covers, over an
     * argument that is itself named. */
    private boolean builtByRule(Core e, Denotations at) {
        if (!(e instanceof Core.PreservedCall call)) {
            return false;
        }
        Built built = BUILT_FROM.get(call.operation());
        return built != null && built.from() < call.args().size()
                && namedByRule(call.args().get(built.from()), at);
    }

    /**
     * Whether {@code e} names something without a guard having to have spoken about it: it is read all
     * the way down. A location is; so is a value composed of ones by a shape the term grammar reads —
     * a concatenation, a conditional, arithmetic, a container the preservation table covers. A call
     * the check has no rule about is not, and neither is anything built from one: nothing follows from
     * naming it, and its construction is left to the run-time check.
     */
    private boolean namedByRule(Core e, Denotations at) {
        if (locationOf(e, at) != null) {
            return true;
        }
        if (e instanceof Core.Read r) {
            return at.of(r.binding()) instanceof Denotes.Term t && t.readable();
        }
        Core read = asOperator(e);
        if (read instanceof Core.PreservedCall call && !readsAsATerm(call)) {
            return builtByRule(read, at);
        }
        // A call the representation did not keep standing answers something this check has no rule
        // about, whatever the operation behind it was.
        if (read instanceof Core.Call || read instanceof Core.Apply) {
            return false;
        }
        // Arithmetic is the numeric domain's to name. Where the domain builds a form, that form is
        // what a clause is read against; where it declines to — a variable product, an integer divide
        // — declining is a decision about what this check reasons over, and reporting a construction
        // it has decided not to reason over would be reporting the decision as the author's to fix.
        if (read instanceof Core.Binary bin && isArith(bin.op())) {
            return false;
        }
        // A conditional is one of its branches and which one is not decided here. Saying only that it
        // is that term reports every construction over one, including where both branches satisfy the
        // clause. Reading it is checking the construction on each branch under its own condition,
        // which this walk does not do, so it is not named until it does.
        if (read instanceof Core.If) {
            return false;
        }
        boolean[] all = {true};
        // A closure is not part of what names the value: the tables are rules about how many elements
        // there are and where they came from, and how each one is made has no bearing on either.
        Core.forEachChild(read, child -> all[0] = all[0]
                && (child instanceof Core.Block || namedByRule(child, at)));
        return all[0];
    }

    /** Whether the check has a rule about what a call answers, rather than only about how to render it. */
    private static boolean readsAsATerm(Core.PreservedCall call) {
        return SIZE_CALLS.contains(call.operation()) || BUILT_FROM.containsKey(call.operation())
                || CARRIED.containsKey(call.operation()) || QUANTIFIERS.contains(call.operation())
                || call.operation().equals(op("Bool.not"));
    }

    // --- what the two representations share ----------------------------------------------------

    /**
     * {@code e} as the value it is written as, for the one reader that is defined over written values:
     * the constant folder. A value written out is the same value in either representation, so this is
     * a rendering and not a second tree — everything computed answers with nothing, and the fold then
     * has nothing to fold.
     */
    private static Ast.Expr asWrittenValue(Core e) {
        return switch (e) {
            case Core.Int i -> new Ast.IntLit(i.value(), i.pos());
            case Core.Decimal d -> new Ast.DecimalLit(d.value(), d.pos());
            case Core.Str s -> new Ast.StringLit(s.value(), s.pos());
            case Core.Bool b -> new Ast.BoolLit(b.value(), b.pos());
            case Core.Neg n -> {
                Ast.Expr operand = asWrittenValue(n.operand());
                yield operand == null ? null : new Ast.Neg(operand, n.pos());
            }
            case Core.Binary b -> {
                Ast.Expr left = asWrittenValue(b.left());
                Ast.Expr right = asWrittenValue(b.right());
                yield left == null || right == null ? null
                        : new Ast.Binary(b.op(), left, right, b.pos());
            }
            case Core.PreservedCall call -> {
                List<Ast.Expr> args = new ArrayList<>();
                for (Core arg : call.args()) {
                    Ast.Expr written = asWrittenValue(arg);
                    if (written == null) {
                        yield null;
                    }
                    args.add(written);
                }
                yield new Ast.Apply(call.operation().name(), call.operation(), args,
                        ConstructionOrigin.own(), call.pos());
            }
            case null, default -> null;
        };
    }

    // --- helpers -------------------------------------------------------------------------------

    /** A read of {@code binder}, as the expression naming the value it holds. */
    private static Core.Read read(Ast.Binder binder, Type type, SourcePos pos) {
        return new Core.Read(binder.name(), binder.id(), type, pos);
    }

    /** The block {@code e} is, following a name given one: a lambda handed to an operation the
     * representation keeps standing is never applied here, so it is bound to a name like any other
     * value and reaches the call as that name. */
    private static Core.Block blockOf(Core e, Denotations at) {
        if (e instanceof Core.Block b) {
            return b;
        }
        return e instanceof Core.Read r && at.valueOf(r.binding()) instanceof Core.Block b ? b : null;
    }

    /** What {@code data}'s fields are, remembered. */
    private Map<String, Type> fieldsOf(Ast.Data data) {
        return fieldsOf.computeIfAbsent(data, d -> TypeOps.fieldTypes(d, symbols));
    }

    /** Which binding each of {@code data}'s fields is, remembered. */
    private Map<String, BindingId> fieldBindingsOf(Ast.Data data) {
        return fieldBindings.computeIfAbsent(data, d -> TypeOps.fieldBindings(d, symbols));
    }

    /** The type of {@code field} read from {@code owner}, or null where that is not a field of a
     * declaration this module can see. */
    private Type fieldType(Type owner, String field) {
        return owner instanceof Type.Ref r && symbols.get(r.name()) instanceof Ast.Data data
                ? fieldsOf(data).get(field) : null;
    }

    /** What a container hands its closure: a list's or set's element, a map's value (the key is the
     * other closure parameter and is not the one the table credits), an option's payload, and a
     * function's first parameter where what is held is the closure itself. */
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
        if (t instanceof Type.FnOf fn && !fn.params().isEmpty()) {
            return fn.params().get(0);
        }
        return null;
    }

    private boolean numericNewtype(Type t) {
        return TypeOps.directNumericNewtypeBase(t, symbols) != null;
    }

    private boolean isNumeric(Type t) {
        return t == Type.INT || t == Type.DECIMAL || numericNewtype(t);
    }

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
