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
import java.util.HashMap;
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

    /** What the guards have settled on the current path: numeric relations, and predicates known to
     * hold or to fail. Threaded functionally through the walk, as the domain alone once was. */
    private record Known(NumericDomain numbers, PredicateFacts facts) {

        static Known top() {
            return new Known(NumericDomain.top(), PredicateFacts.none());
        }

        Known with(NumericDomain n) {
            return new Known(n, facts);
        }

        Known with(PredicateFacts f) {
            return new Known(numbers, f);
        }

        Known forgetIf(java.util.function.Predicate<String> drop) {
            return new Known(numbers.forgetIf(drop), facts.forgetIf(drop));
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
            return "it calls `" + call.fn() + "`, which the check reads as a value and not as a term";
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

    /** Analyzes one behavior body against its input types. Never throws. A {@code null} source is a
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
            c.walk(source.body(), k, new HashMap<>(params));
        } catch (RuntimeException _) {
            // fail-open: the run-time invariant check remains the backstop
        }
        return new Findings(c.errors, c.warnings);
    }

    // --- the walk ------------------------------------------------------------------------------

    private void walk(Ast.Expr e, Known k, Map<String, Type> types) {
        checkIfConstruction(e, k, types, false);
        switch (e) {
            case Ast.If iff -> {
                walk(iff.cond(), k, types);
                walk(iff.then(), assumeCond(iff.cond(), k, types, true), types);
                walk(iff.els(), assumeCond(iff.cond(), k, types, false), types);
            }
            case Ast.IfConstructed ic -> {
                // The attempt's own construction cannot abort — a failing invariant is the else
                // branch — so it is checked for a decided violation and never warned about as a
                // possible one. Its field values are walked on their own so a construction nested
                // inside an argument is still an ordinary, aborting one.
                checkIfConstruction(ic.construct(), k, types, true);
                Ast.forEachChild(ic.construct(), child -> walk(child, k, types));
                Map<String, Type> t2 = new HashMap<>(types);
                Known k2 = rebind(k, ic.binderName());
                Type built = typeExpr(ic.construct(), types);
                if (built != null) {
                    t2.put(ic.binderName(), built);
                    k2 = seedParam(ic.binderName(), built, k2);   // on this branch the invariant holds
                }
                walk(ic.then(), k2, t2);
                // Each departure stands where the invariant did not hold, and nothing was built
                // there, so none of them is seeded with anything the attempt would have guaranteed.
                ic.els().forEach(arm -> walk(arm.body(), k, types));
            }
            case Ast.LetIn li -> {
                walk(li.value(), k, types);
                Map<String, Type> t2 = new HashMap<>(types);
                Type vt = typeExpr(li.value(), types);
                if (vt != null) {
                    t2.put(li.name(), vt);
                }
                LinearForm vf = affineOf(li.value(), types);
                Known k2 = rebind(k, li.name());
                if (isNumeric(vt) && vf != null) {
                    k2 = k2.with(k2.numbers().assign(li.name(), vf));
                }
                walk(li.body(), k2, t2);
            }
            case Ast.Match m -> {
                walk(m.scrutinee(), k, types);
                for (Ast.Case c : m.cases()) {
                    Map<String, Type> t2 = new HashMap<>(types);
                    Known k2 = k;
                    if (c.binding() != null) {
                        k2 = rebind(k, c.bindingName());
                        if (c.caseTypes().size() == 1) {
                            Type bound = MatchElaborator.caseBindType(c.caseTypes().get(0).denotes());
                            if (bound != null) {
                                t2.put(c.bindingName(), bound);
                            }
                        }
                    }
                    walk(c.body(), k2, t2);
                }
            }
            case Ast.Apply call -> walkCall(call, k, types);
            default -> Ast.forEachChild(e, child -> walk(child, k, types));
        }
    }

    /** Walks a call, binding a combinator closure's element parameter to the list's element type (and
     * seeding its invariant) so a construction inside the closure is analyzed rather than left opaque. */
    private void walkCall(Ast.Apply call, Known k, Map<String, Type> types) {
        Combinator combo = COMBINATORS.get(call.fn());
        for (int i = 0; i < call.args().size(); i++) {
            Ast.Expr arg = call.args().get(i);
            if (combo != null && i == combo.closureArg() && arg instanceof Ast.Block step
                    && combo.elementParam() < step.params().size()
                    && combo.listArg() < call.args().size()) {
                Type elem = elementType(typeExpr(call.args().get(combo.listArg()), types));
                Map<String, Type> t2 = new HashMap<>(types);
                String p = step.params().get(combo.elementParam()).name();
                Known k2 = rebind(k, p);
                if (elem != null) {
                    t2.put(p, elem);
                    k2 = seedParam(p, elem, k2);   // the element carries its type's invariant
                }
                walk(step.body(), k2, t2);
            } else {
                walk(arg, k, types);
            }
        }
    }

    // --- construction detection & discharge check ----------------------------------------------

    private void checkIfConstruction(Ast.Expr e, Known k, Map<String, Type> types,
                                     boolean attempted) {
        switch (e) {
            case Ast.NewData nd when nd.spreads().isEmpty() -> {
                if (symbols.get(nd.typeName().denotes()) instanceof Ast.Data type) {
                    Map<String, LinearForm> forms = new HashMap<>();
                    Map<String, String> paths = new HashMap<>();
                    Map<String, Ast.Expr> given = new HashMap<>();
                    Function<Ast.Expr, String> bodyKey = value -> siteKey(value, types);
                    for (Ast.FieldInit fi : nd.inits()) {
                        LinearForm f = affineOf(fi.value(), types);
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
                if (typeExpr(bin, types) instanceof Type.Ref r
                        && symbols.get(r.name()) instanceof Ast.Data type && type.newtype()) {
                    LinearForm value = affineOf(bin, types);
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

    private static List<String> firstOnly(List<String> keys) {
        return keys.isEmpty() ? keys : List.of(keys.get(0));
    }

    /** Refines {@code k} by asserting {@code cond} (or its negation): a comparison tightens the
     * numeric domain, a stdlib predicate settles a fact. A condition of neither shape, and an operand
     * outside the affine fragment, leave {@code k} unchanged (sound). */
    private Known assumeCond(Ast.Expr rawCond, Known k, Map<String, Type> types, boolean positive) {
        Ast.Expr cond = asSizeComparison(rawCond);
        // `&&` asserted true gives both sides; `||` asserted false gives both sides negated.
        if (cond instanceof Ast.Binary b
                && (b.op() == Ast.BinOp.AND && positive || b.op() == Ast.BinOp.OR && !positive)) {
            return assumeCond(b.right(), assumeCond(b.left(), k, types, positive), types, positive);
        }
        Ast.Expr under = negated(cond);
        if (under != null) {
            return assumeCond(under, k, types, !positive);
        }
        Known out = k;
        // What holds of the sizes the condition names, whichever way the condition itself is read.
        List<Constraint> known = new ArrayList<>();
        sizeFacts(cond, types, known);
        for (Constraint c : known) {
            out = out.with(out.numbers().assume(c.form(), c.rel()));
        }
        if (cond instanceof Ast.Binary b) {
            Rel rel = relOf(b.op());
            Rel eff = rel == null ? null : positive ? rel : negateRel(rel);
            LinearForm la = eff == null ? null : affineOf(b.left(), types);
            LinearForm ra = eff == null ? null : affineOf(b.right(), types);
            if (la != null && ra != null) {
                out = out.with(out.numbers().assume(la.minus(ra), eff));
            }
        }
        // Both routes, always: which one carries a clause is decided where the clause is read, and a
        // guard does not know which that will be.
        Polar polar = polar(cond, positive);
        String key = bodyKey(polar.expr(), types);
        return key == null ? out : out.with(out.facts().assume(key, polar.positive()));
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
        if (e instanceof Ast.Apply call && "Bool.not".equals(call.fn()) && call.args().size() == 1) {
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
        for (Ast.InvariantClause inv : invariantsOf(ref.name(), data)) {
            List<Clause> o = obligations(inv.expr(), binds);
            if (o == null) {
                continue;
            }
            for (Clause c : o) {
                for (Constraint known : c.known()) {
                    out = out.with(out.numbers().assume(known.form(), known.rel()));
                }
                if (c.numeric() != null) {
                    out = out.with(out.numbers().assume(c.numeric().form(), c.numeric().rel()));
                }
                if (c.fact() != null) {
                    // What an input's type guarantees is guaranteed of the term as written; a
                    // container built from it is another term, and reads the rules where it is
                    // constructed rather than here.
                    out = out.with(out.facts().assume(c.fact().keys().get(0), c.fact().positive()));
                }
            }
        }
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

    /** The shared affine walk: literals and {@code +}/{@code -} compose; every other node is handed to
     * {@code leaf} (which decides whether it is an atom, a resolved field, or opaque). */
    private LinearForm affine(Ast.Expr e, Function<Ast.Expr, LinearForm> leaf) {
        return switch (e) {
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
    private LinearForm affineOf(Ast.Expr e, Map<String, Type> types) {
        return affine(e, n -> {
            if (n instanceof Ast.NewData nd && nd.spreads().isEmpty() && nd.inits().size() == 1
                    && nd.inits().get(0).name().equals("value")
                    && numericNewtype(Type.ref(nd.typeName().denotes()))) {
                return affineOf(nd.inits().get(0).value(), types);
            }
            String atom = atomOf(n, types);
            return atom == null ? null : LinearForm.atom(atom);
        });
    }

    /** The leaf rule for an invariant expression: a bare name resolves to its field/{@code value}, and
     * a size call over one to that container's size atom. */
    private Function<Ast.Expr, LinearForm> resolveLeaf(Bindings binds) {
        return n -> {
            String size = clauseSizeAtom(n, binds);
            if (size != null) {
                return LinearForm.atom(size);
            }
            return n instanceof Ast.Var v ? binds.form().apply(v.name()) : null;
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

    /** The atom a size call in a clause names, or {@code null}. */
    private String clauseSizeAtom(Ast.Expr e, Bindings binds) {
        if (!(e instanceof Ast.Apply call) || !SIZE_CALLS.contains(call.fn()) || call.args().size() != 1) {
            return null;
        }
        Named named = resolve(call.args().get(0), binds, true);
        String key = named.key().apply(named.term());
        return key == null ? null : call.fn() + "(" + key + ")";
    }

    /** The path an invariant expression names at the construction site: a bare field name through the
     * bindings, then plain field steps. */
    private String invPath(Ast.Expr e, Bindings binds) {
        // A clause is a path over the declaration's own fields, read by the very rule a body path is
        // read by — so a newtype's `.value` is the same location on both sides — and then the field it
        // is rooted at is replaced by what the construction is giving that field. One rule for what a
        // location is, applied twice, rather than two rules that have to be kept agreeing.
        String local = pathKey(e, binds.fields());
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
    private String atomOf(Ast.Expr e, Map<String, Type> types) {
        String size = sizeAtom(e, arg -> bodyKey(arg, types));
        if (size != null) {
            return size;
        }
        return isNumeric(typeExpr(e, types)) ? pathKey(e, types) : null;
    }

    /** A body expression's canonical key: a location names itself, and everything else is read
     * structurally. */
    private String bodyKey(Ast.Expr e, Map<String, Type> types) {
        return termKey(e, x -> pathKey(x, types), Map.of(), 0);
    }

    /**
     * How a value a construction is being given is named where a clause reads it: a location names
     * itself, and a container built from one by an operation the table covers names that
     * construction. Anything else names nothing.
     *
     * <p>The restriction is what ties the flagging to the rules. A value the check has no rule about
     * — a string joined from parts, a number a helper returned — can be rendered, but nothing follows
     * from rendering it, and reporting its construction would be reporting a possible violation the
     * author has no reasonable guard for.
     */
    private String siteKey(Ast.Expr e, Map<String, Type> types) {
        String path = pathKey(e, types);
        if (path != null) {
            return path;
        }
        if (e instanceof Ast.Apply call) {
            Built built = BUILT_FROM.get(call.fn());
            if (built != null && built.from() < call.args().size()
                    && siteKey(call.args().get(built.from()), types) != null) {
                return bodyKey(e, types);
            }
        }
        return null;
    }

    /** The atom key of {@code SIZE_CALL(container)} when {@code key} can name the container, else
     * {@code null}. */
    private static String sizeAtom(Ast.Expr e, Function<Ast.Expr, String> key) {
        if (!(e instanceof Ast.Apply call) || !SIZE_CALLS.contains(call.fn()) || call.args().size() != 1) {
            return null;
        }
        String arg = key.apply(sizeSource(call.args().get(0)));
        return arg == null ? null : call.fn() + "(" + arg + ")";
    }

    /** The container a size is really the size of: an operation that keeps the size of what it was
     * built from is peeled away, so {@code List.length(List.map(f, xs))} is the atom
     * {@code List.length(xs)}. How the elements are made has no bearing on how many there are, which
     * is why the closure does not enter the key. */
    private static Ast.Expr sizeSource(Ast.Expr e) {
        if (e instanceof Ast.Apply call) {
            Built built = BUILT_FROM.get(call.fn());
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
        if (SIZE_CALLS.contains(call.fn()) && call.args().size() == 1) {
            Named named = resolve(call.args().get(0), binds, true);
            String atom = clauseSizeAtom(e, binds);
            if (atom != null) {
                out.add(new Constraint(LinearForm.atom(atom), Rel.GE));   // a size is never negative
                bounds(call.fn(), named.term(), named.key(), out);
            }
        }
        for (Ast.Expr arg : call.args()) {
            sizeFacts(arg, binds, out);
        }
    }

    /** The same, over a body expression, where a term is only ever itself. */
    private void sizeFacts(Ast.Expr e, Map<String, Type> types, List<Constraint> out) {
        sizeFacts(e, Bindings.ofBody(x -> bodyKey(x, types)), out);
    }

    /** {@code size(c) <= size(what c was built from)}, down the chain, wherever the building can only
     * drop elements. */
    private void bounds(String sizeCall, Ast.Expr container, Function<Ast.Expr, String> key,
                        List<Constraint> out) {
        if (!(container instanceof Ast.Apply call)) {
            return;
        }
        Built built = BUILT_FROM.get(call.fn());
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
        Carried carried = CARRIED.get(call.fn());
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
            Built built = BUILT_FROM.get(inner.fn());
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
        Integer at = PROJECTION_OF.get(stated.fn());
        if (built.shape() != Shape.MAPS || at == null || at >= stated.args().size()) {
            return null;
        }
        // Where the mapping's closure is written is already stated once, by the table that says which
        // argument each combinator hands its elements to.
        Combinator combo = COMBINATORS.get(inner.fn());
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
        return new Ast.Apply(call.function(), args, call.origin(), call.pos());
    }

    /** An emptiness check as the comparison it means, or {@code e} unchanged. */
    private static Ast.Expr asSizeComparison(Ast.Expr e) {
        if (e instanceof Ast.Apply call && call.args().size() == 1
                && EMPTINESS.containsKey(call.fn())) {
            Ast.Apply size = new Ast.Apply(EMPTINESS.get(call.fn()), call.denotes(), call.args(),
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
    private String termKey(Ast.Expr e, Function<Ast.Expr, String> site, Map<String, String> bound,
                           int depth) {
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
            case Ast.Apply c when Prelude.hasQualified(c.fn()) ->
                    elementsKey(c.fn() + "(", c.args(), site, bound, depth, ")");
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

    private String pathKey(Ast.Expr e, Map<String, Type> types) {
        return switch (e) {
            case Ast.Var v -> v.name();
            case Ast.FieldAccess fa -> {
                Type owner = typeExpr(fa.target(), types);
                if (fa.field().equals("value") && TypeOps.isSingleValueNewtype(owner, symbols)) {
                    yield pathKey(fa.target(), types);   // a newtype's .value is the same location
                }
                String base = pathKey(fa.target(), types);
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

    private Type typeExpr(Ast.Expr e, Map<String, Type> types) {
        return switch (e) {
            case Ast.IntLit _ -> Type.INT;
            case Ast.DecimalLit _ -> Type.DECIMAL;
            case Ast.Var v -> types.get(v.name());
            case Ast.FieldAccess fa -> {
                Type owner = typeExpr(fa.target(), types);
                yield owner instanceof Type.Ref r && symbols.get(r.name()) instanceof Ast.Data d
                        ? TypeOps.fieldTypes(d, symbols).get(fa.field()) : null;
            }
            case Ast.NewData nd -> Type.ref(nd.typeName().denotes());
            case Ast.LetIn li -> {
                Map<String, Type> inner = new HashMap<>(types);
                Type bound = typeExpr(li.value(), types);
                if (bound == null) {
                    inner.remove(li.name());
                } else {
                    inner.put(li.name(), bound);
                }
                yield typeExpr(li.body(), inner);
            }
            case Ast.Neg n -> typeExpr(n.operand(), types);
            case Ast.Binary b when isArith(b.op()) -> arithType(b, types);
            default -> null;
        };
    }

    /** The result type of an arithmetic binary: the newtype for closed {@code +}/{@code -}
     * (via the checker's shared rule), else the numeric base, else {@code null}. */
    private Type arithType(Ast.Binary b, Map<String, Type> types) {
        Type lt = typeExpr(b.left(), types);
        Type rt = typeExpr(b.right(), types);
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
