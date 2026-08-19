package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.check.Combinators.Handed;
import souther.compiler.check.PathEngine.Entered;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.InvariantMessage;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.Supporting;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.SequencedMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * The intraprocedural invariant-discharge check (spec §invariant-discharge). It walks a behavior's
 * body threading what holds where it stands ({@link Known}), seeded from the input types'
 * invariants and refined along each {@code guard}/{@code if} guard (a {@code guard} is already an
 * {@code if} here). At every construction whose invariant it can carry, it asks whether what is known
 * there <em>discharges</em> it, or refutes it. A construction proven to violate its invariant on a
 * reachable path is a compile error (the path-sensitive generalization of the constant check
 * {@code Amount(-5)}); one it cannot prove is a warning (a possible abort — guard it, or reify the
 * relation into a type invariant). An invariant naming something it cannot name is left opaque (no
 * diagnostic; the run-time check stays), so every flagged construction is one whose clauses could be
 * read at the values it is being given.
 *
 * <p>A violation is reported in the terms it was reached in, and no stronger: {@link Known} carries
 * beside itself the reading with nothing a condition on the path settled, and a clause that reading
 * already refutes is one the construction fails wherever it is written. Which of the things known
 * here settled the rest is not asked — nothing records what a refutation used, so a violation the
 * values alone do not settle is said that way and not blamed on a guard.
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
 * <p>What is here is the walk: where to look, what is known where, and what to say about a
 * construction. What it looks <em>with</em> is beside it — {@link DischargeRules} for what the
 * language's operations keep, {@link Clauses} for a declaration's invariant read at a value,
 * {@link Terms} for where a value is and what can be said of it, {@link Predicates} for what a clause
 * owes and what a guard settles. Each of those is a question with one answer, and the walk is what
 * asks them in order.
 *
 * <p>The walk mirrors {@link TotalityChecker}: a {@code switch} over {@link Core} threading an
 * immutable environment. It is fail-open for what it cannot analyze — an expression or a shape it
 * has no rule for is swallowed, so a limit of this analysis can never reject a valid program. It is
 * not fail-open for this analysis disagreeing with itself: {@link Terms.OneTermTwoKinds} says one
 * name was given two values, and swallowing it produces a behavior with no findings, which is what a
 * behavior whose invariants all discharge produces. That one is rethrown ({@link #gaveUp}).
 */
public final class InvariantChecker {

    /**
     * What one analysis came to.
     *
     * <p>{@code status} is not about the model. It says whether the findings are all of the findings
     * there were: this check is fail-open for what it cannot read, so an analysis that fell over on
     * one of those produces exactly what an analysis that finished and found nothing produces, and a
     * consumer reading only the two lists cannot tell them apart. Production does not need to — the run-time check is the backstop
     * either way — but a test asserting that a construction is discharged is asserting something
     * about an analysis that ran, and without this it would pass just as well on one that did not.
     */
    record Findings(List<CompileException> errors, List<Diagnostic> warnings, Status status) {}

    /** Whether an analysis produced all of the findings there were. {@code ABANDONED} covers both a
     * walk that fell over and a body there was none of: neither ran to the end, and the findings are
     * as complete in one case as in the other, which is not at all. */
    enum Status { COMPLETE, ABANDONED }

    /** One analysis that fell over, and what it fell over on. */
    record GaveUp(String where, RuntimeException why) {}

    /**
     * Where a test in this package reads the analyses that fell over, and null everywhere else.
     *
     * <p>Beside {@link #WATCHING} and for the same reason. Falling over is silent by design: the
     * catch that makes this check unable to reject a valid program also makes it unable to say it
     * stopped. A body with no discharge to run is not recorded here — there was nothing to fall over
     * on — so what lands here is only what the analysis could not get through.
     */
    static List<GaveUp> GAVE_UP;

    /**
     * One construction and what this check found on it: the verdict on the invariant, and the names
     * it could have written out on either side of it.
     *
     * <p>The whole judgment and not the verdict alone, so that a test can hold the two apart. What a
     * clause with no name costs is a name and not a judgment, and read from a rendered warning that
     * difference is only visible where the wording changes.
     */
    record Said(String type, SourcePos pos, Judgment judgment) {

        Verdict verdict() {
            return judgment.verdict();
        }
    }

    /**
     * Where a test in this package reads the verdicts a check reached, and null everywhere else.
     *
     * <p>What the check <em>says</em> is its findings, and a verdict is not one of them: two of the
     * four are silent, and which of those two a construction came out as is exactly what no
     * diagnostic reports. A test holding that difference has nowhere else to read it, and a
     * distinction nothing can read is one that stops being true without anything failing.
     */
    static List<Said> WATCHING;

    /**
     * What this check reads: one behavior's body and the invariants of the types around it, both in
     * the representation the rules are written at ({@link InliningPolicy#DISCHARGE}) rather than the
     * one the backend emits from.
     *
     * <p>{@code invariants} holds the clauses of the module being checked. A type another module
     * declares is not among them and its clauses are read off its declaration, which for a module
     * reached through its published classes is the declaration that module published, read back by
     * this front end (spec §published-modules). Either way the clause read here is the rule its
     * author wrote, so where a declaration was written does not decide what can be discharged
     * against it (spec §invariant-discharge-representation).
     */
    public record Source(Hir.Expr body, Map<TypeSymbol, List<Hir.InvariantClause>> invariants,
                         Map<ValueName.Behavior, StatedContract> contracts) {

        public Source {
            contracts = Map.copyOf(contracts);
        }
    }

    /**
     * How many readings of a body one path down its case splits may cost, before the rest is left to
     * the run-time check.
     *
     * <p>Counted in readings and not in splits opened. The two were one number for as long as every
     * split had two arms: three nested {@code if}s are eight readings, which is what this bound used
     * to be written as. A {@code match} has an arm per case, so the same three of them over a sum of
     * twelve is one thousand seven hundred and twenty-eight — the same bound naming a cost two orders
     * of magnitude apart, which is a bound that stopped saying what it was for.
     *
     * <p>What is asked of a split is what opening it would bring the path to, and not what the path
     * has come to already ({@link #opens}). Read the second way a path fifteen readings long admits
     * a split of any width at all, and the bound bounds the path before the widest split on it
     * rather than the path.
     *
     * <p>Sixteen, which is what a sum of eight cases costs with one conditional inside an arm.
     * Below that, opening a {@code match} spends enough of the bound that a conditional written in a
     * value position inside one of its arms is refused — and that conditional was opened before this
     * check read {@code match}es at all, by lifting it out of the arm. A bound that turns a
     * construction which discharged into one that is owed is the reading getting worse at a shape it
     * was not asked about. It also lets a fourth conditional be opened where three were opened
     * before, which is the same bound spent on the shape it was written for.
     */
    private static final int READINGS_A_PATH_MAY_COST = 16;


    /** The rules this check reads a program by: entering a binding, taking a condition as holding,
     * and reading what a type guarantees. Held apart from the check ({@link PathEngine}) because the
     * question they add up to — can anything stand here — has more than this one reader, and a
     * second walk deriving it again would be a second set of rules. */
    private final PathEngine engine;
    private final Symbols symbols;
    /** The declarations' invariants, typed where they are declared and read where a value is built. */
    private final Clauses clauses;
    /** Where a value is, what it is called, and what can be said of it. */
    private final Terms terms;
    /** What a clause owes and what a guard settles. */
    private final Predicates predicates;
    private final List<CompileException> errors = new ArrayList<>();
    private final List<Diagnostic> warnings = new ArrayList<>();

    private InvariantChecker(Symbols symbols,
                             Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants) {
        this(symbols, dischargeInvariants, Map.of());
    }

    private InvariantChecker(Symbols symbols,
                             Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants,
                             Map<ValueName.Behavior, StatedContract> contracts) {
        this.engine = new PathEngine(symbols, dischargeInvariants, contracts);
        // Named here because this check reads them directly and often. They are the engine's, not a
        // second copy: one engine builds them once and everything below sees those.
        this.symbols = engine.symbols();
        this.clauses = engine.clauses();
        this.terms = engine.terms();
        this.predicates = engine.predicates();
    }

    /**
     * How a clause of {@code data}'s invariant can be discharged, read on its own — the construction
     * is assumed to name what it is given, so what is left is the clause's own shape. {@code at} is
     * where the clause is written, which is the pre-expansion position; {@code clause} is that clause
     * in the representation the check reads.
     */
    public static List<ClauseDischarge> capabilitiesOf(ClausesForDischarge.ClauseReading clause,
                                               TypeSymbol named, Hir.Data data, Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols, Map.of());
        // Read over the declaration's own fields, each standing for itself: a construction hands one
        // value per field, so a clause naming a field names something wherever it is built. These
        // stand for a value rather than holding one, so they are entered as locations and nothing is
        // seeded of them — what a clause owes is the question, and answering it here would be
        // assuming it.
        return c.capabilitiesOf(clause, read -> c.clauses.typed(read, named, data),
                Denotations.none().locations(c.clauses.bindingsOf(named, data).values(),
                        c.terms::placeSubject, c.terms::placeTerm),
                data.name());
    }

    /**
     * How a statement of the model can be discharged, read on its own: what the check can make of it
     * where the names in it stand for themselves.
     *
     * <p>Not a question about invariants. A data's clause and a behavior's rule are the same
     * expression fragment read the same way, and what tells them apart — which names stand for what,
     * and where those names come from — is settled by {@code locations} before this is asked. Held
     * here because the answer is what this check can read, and a second reader working that out from
     * the outside would be deciding it by what it happened to manage.
     *
     * <p>More than one where more than one is true of it. What is written as one thing can be read as
     * several — a rule that names a helper is one thing to its author and is whatever that helper
     * states to this — and the readings need not agree: a bound and a term the check can only compare
     * are discharged by different guards, and one of them being there says nothing about the other.
     * Answering with one of them would be picking which half of a clause to describe, and the half not
     * picked is the one an author is about to be surprised by.
     *
     * <p>Where the answers are said is the clause's and is not passed in. A position that can be
     * passed can be passed from the wrong tree — which is what an expansion of the clause is, and
     * what every reader of this had to be told not to take it from. Handed the clause itself, there
     * is nothing left to get wrong: it says where it was written and what it comes to, and the two
     * were made together ({@link ClausesForDischarge}).
     *
     * @param clause the conjunct, as written and as this check reads it
     * @param typing what types the read form here — a declaration's fields, a signature's names —
     *               answering null where this compiler could not type it
     * @param locations the names it may read, each standing for itself
     * @param describing what is being read, for the record a fail-open leaves behind
     */
    static List<ClauseDischarge> capabilitiesOf(StatedContract.Conjunct conjunct,
                                        Denotations locations, Symbols symbols, String describing) {
        return new InvariantChecker(symbols, Map.of())
                .capabilitiesOf(conjunct.stated(), conjunct.at(), locations, describing);
    }

    /** What turns the read form of a clause into the tree this check walks, which is the reader's to
     * say: a declaration's clause is typed over its fields and a behavior's rule over its signature. */
    @FunctionalInterface
    interface Typing {
        Core type(Hir.Expr read);
    }

    private List<ClauseDischarge> capabilitiesOf(ClausesForDischarge.ClauseReading clause,
                                         Typing typing, Denotations locations, String describing) {
        return capabilitiesOf(typed(typing, clause.read(), describing), clause.at(), locations,
                describing);
    }

    /**
     * {@code read} as its reader types it, or null where it could not be typed there.
     *
     * <p>Fail-open, as the walk is, and recorded for the reason the reading below is: a clause this
     * compiler could not type and an analysis that fell over typing it both come out
     * {@code runtimeOnly}, and only one of them is something the model says.
     */
    private Core typed(Typing typing, Hir.Expr read, String describing) {
        try {
            return typing.type(read);
        } catch (RuntimeException why) {
            gaveUp("typing " + describing, why);
            return null;
        }
    }

    private List<ClauseDischarge> capabilitiesOf(Core stated, SourcePos at, Denotations locations,
                                         String describing) {
        List<ClauseDischarge> found = new ArrayList<>();
        for (ClauseDischarge.Kind read : kindsRead(stated, locations, describing)) {
            found.add(read == ClauseDischarge.Kind.RUNTIME_ONLY
                    ? ClauseDischarge.runtimeOnly(at, whyUnreadable(stated, locations))
                    : new ClauseDischarge(at, read, java.util.Optional.empty()));
        }
        return List.copyOf(found);
    }

    /** What the check made of {@code stated}, said as the readings it got and nothing about where
     * they belong. */
    private List<ClauseDischarge.Kind> kindsRead(Core stated, Denotations locations,
                                                 String describing) {
        Predicates.Owed owed;
        try {
            owed = stated == null ? Predicates.Owed.UNREADABLE
                    : predicates.obligations(stated, Known.top(), locations, false);
        } catch (RuntimeException why) {
            // Fail-open, as the walk is — and recorded, because a clause this could not read and an
            // analysis that fell over reading it both come out `runtimeOnly`, and only one of them
            // is something the model says.
            gaveUp("capabilitiesOf " + describing, why);
            owed = Predicates.Owed.UNREADABLE;
        }
        boolean asABound = false;
        boolean asATerm = false;
        for (Predicates.Clause owe : owed.clauses()) {
            // A clause read both ways is one obligation with two readings of it, not two obligations
            // — the bound is the stronger of them, and any guard implying it discharges the clause,
            // so that is what it is here.
            if (owe.numeric() != null) {
                asABound = true;
            } else {
                asATerm = true;
            }
        }
        // What was not read at all is said even where something else was: a clause half of which
        // could not be read would otherwise be described entirely by the half that was.
        return ClauseDischarge.kindsRead(asABound, asATerm, owed.unreadable());
    }

    /** What in {@code clause} the check cannot read, said so an author can act on it. */
    private String whyUnreadable(Core clause, Denotations fields) {
        if (clause == null) {
            return "it is not a rule this check could read as one expression";
        }
        Core blocked = unreadable(clause, fields);
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
     * of it. Read under the same fields the clause was, so a field it names is a location and what
     * is left is the shape. */
    private Core unreadable(Core e, Denotations fields) {
        Core[] found = {null};
        Core.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = unreadable(child, fields);
            }
        });
        if (found[0] != null) {
            return found[0];
        }
        return terms.bodyKey(e, fields) == null ? e : null;
    }

    /**
     * What the invariants reaching a value of {@code data} leave each of its fields able to hold, and
     * the atom each field is named by.
     *
     * <p>The same seeding a parameter of that type gets ({@link #seedAt}), read for what it says of
     * the values instead of for what it discharges. A record's own clause relates its fields; each
     * field's type bounds that field on its own; and both land in one state over the same atoms,
     * which is what lets a bound reach one field through another.
     *
     * @param constraints everything the clauses were read as, whichever domain each of them reached.
     *                    The whole state and not one domain of it: what a caller asks of a
     *                    declaration is whether any value of it exists, and that is a question about
     *                    all of them at once ({@link ConstraintState#isBottom})
     * @param atoms the atom each field's own value is, for the fields that are numbers
     * @param keys what each field is called where it is not a number — which every named position
     *             has, and which a number has as well. A position is looked up by both, since a
     *             clause reaching it may be recognised by either
     * @param held the atom the count of each field is, for the fields whose values are counted by
     *             something. A field is in one of these two or in neither, never in both: what
     *             names a number is its own value and what names a list is how much of it there is
     * @param everyClauseRead whether every clause of the declaration was taken into the domain. False
     *                        where one could not be typed or held nothing this reads — the bounds are
     *                        then weaker than what the declaration actually says, and a caller
     *                        turning one into an obligation has to know that
     * @param notGathered where a clause of the value did not reach the readings at all, as the
     *                 paths the stops happened at. A clause that could not be typed, and a walk
     *                 that declined to go further: in both, a rule of the declaration is one no
     *                 reading here ever saw, so no reading can say it took that part of the
     *                 declaration in.
     *
     *                 <p>Where and not whether, because a rule that narrows a position names it,
     *                 and a clause written under one field can name no position outside that field.
     *                 Recorded as one flag for the value, a stop under a regex-bounded code spoiled
     *                 the plain {@code Int} beside it, and a report said a rule about that
     *                 {@code Int} may have gone unread when nothing was written about it at all.
     *                 A stop at {@link FieldDomains#THE_VALUE} is the declaration's own clause and
     *                 does reach every position of it.
     *
     *                 <p>A different question from {@code everyClauseRead}, which is one reading's
     *                 account of the clauses it was handed: a clause that reading could not turn
     *                 into an obligation is one another reading may have taken in whole, and
     *                 borrowing that answer would settle each reading's completeness by a fragment
     *                 that is not its own
     */
    record Seeded(ConstraintState constraints, Map<String, FactSubject> atoms, Map<String, FactSubject> keys,
                  Map<String, FactSubject> held, Reading reading, ReadingEvidence took,
                  boolean everyClauseRead, Set<String> notGathered) {

        public Seeded {
            notGathered = Set.copyOf(notGathered);
        }

        /** What a walk that fell over comes to: no position named, no rule read, and saying so of
         *  every position, since nothing here knows which of them the rules were about. */
        static Seeded nothingRead() {
            return new Seeded(ConstraintState.top(), Map.of(), Map.of(), Map.of(),
                    new Reading(List.of(), Map.of(), Map.of()), new ReadingEvidence(), false,
                    Set.of(FieldDomains.THE_VALUE));
        }

        /** The numbers alone, for the readers that are about intervals. Whether a value exists is
         * asked of {@link #constraints} and is never read off this. */
        NumericDomain<FactSubject> numbers() {
            return constraints.numbers();
        }
    }

    /** {@link Seeded} for one declaration. A declaration this cannot read is one whose fields it says
     * nothing about, which is the same answer as a declaration with no rules — so nothing about the
     * declaration throws. {@link Terms.OneTermTwoKinds} is not about the declaration and is not
     * caught ({@link #gaveUp}). */
    /**
     * How far a seeding reads at each name it meets.
     *
     * <p>Two questions and not one. Leaving a declaration's own clauses out is what a reader asking
     * which declaration moved an end does: everything under that name still guarantees what it
     * guarantees, and only the one clause is taken away. Stopping at a name is what a reader
     * supposing that name has values does: nothing under it is read at all, because what is under it
     * is exactly what leaves it without them.
     *
     * <p>Told apart because one of them was doing for both. A name whose own clauses were skipped
     * was still descended into, so a value supposed to exist came back impossible by the rules of
     * what it wraps — the supposing undone one step in, by the same walk that honoured it.
     *
     * @param withoutClauses which declarations' own clauses are left out, what is under them still
     *                       being read
     * @param stopAt         which declarations are not read at all
     */
    record Reach(java.util.function.Predicate<TypeSymbol> withoutClauses,
                 java.util.function.Predicate<TypeSymbol> stopAt) {

        /** Every rule, wherever it is written. */
        static final Reach EVERYTHING = new Reach(_ -> false, _ -> false);

        /** Every rule but the ones {@code these} names wrote. */
        static Reach withoutClausesOf(java.util.function.Predicate<TypeSymbol> these) {
            return new Reach(these, _ -> false);
        }

        /** Every rule that is not reached through one of {@code these}, they being supposed to hold
         * values whatever is written under them. */
        static Reach stoppingAt(java.util.function.Predicate<TypeSymbol> these) {
            return new Reach(_ -> false, these);
        }
    }

    static Seeded seedFields(TypeSymbol named, Hir.Data data, Symbols symbols) {
        return seedFields(named, data, symbols, Map.of());
    }

    /**
     * {@link Seeded} with some of the fields already settled at a value.
     *
     * <p>What is left for the others, given those. The same domain and the same closure — settling a
     * field is one more assertion into it — so what comes back is the range each remaining field can
     * still take, which is where a row completing that assignment has to look.
     */
    static Seeded seedFields(TypeSymbol named, Hir.Data data, Symbols symbols,
                             Map<String, Count> settled) {
        return seedFields(named, data, symbols, settled, Reach.EVERYTHING);
    }

    /**
     * The same, reading only as far as {@code reach} says at each name it meets.
     *
     * <p>What a rule did is read by asking what happens without it. Which clause moved an edge is not
     * something the closure records — it answers with a number and not with how it got there — and
     * this is that question put to the same reader rather than answered by a second one: seed the
     * value again without one declaration's clauses, and an end that moves is an end that
     * declaration was holding. Supposing a declaration has values is the other thing {@code reach}
     * says, and it is not that one — see {@link Reach}.
     */
    static Seeded seedFields(TypeSymbol named, Hir.Data data, Symbols symbols,
                             Map<String, Count> settled, Reach reach) {
        InvariantChecker c = new InvariantChecker(symbols, Map.of());
        Map<String, Type> fields = c.clauses.fieldsOf(data);
        Map<String, BindingId> bindings = c.clauses.bindingsOf(named, data);
        Denotations at = Denotations.none()
                .locations(bindings.values(), c.terms::placeSubject, c.terms::placeTerm);
        Known k = Known.top();
        boolean read = true;
        // A clause nothing could type never reaches `written`, so no reading below sees it and none
        // of them can spoil a position for it. That is a fact about what was handed over rather
        // than about any one reading, and it is recorded here where the handing over happens.
        Set<String> notGathered = new LinkedHashSet<>();
        List<Written> written = new ArrayList<>();
        ReadingEvidence took = new ReadingEvidence();
        Gathering gathering = new Gathering() {

            @Override
            public void gathered(RuleRef.Invariant from, Core clause,
                                 Set<FactSubject> spokenFor) {
                written.add(new Written(from, clause));
                spokenFor.forEach(spoken -> took.record(from, spoken));
            }

            @Override
            public void missed(String path) {
                notGathered.add(path);
            }
        };
        try {
            boolean own = !reach.withoutClauses().test(named) && !reach.stopAt().test(named);
            if (!own && !c.clauses.of(named, data).isEmpty()) {
                // Left out because this reading was asked to leave them out, which is still a rule
                // of the value that no reading here took in. At the value itself, since a clause of
                // this declaration can name any position of it.
                gathering.missed(FieldDomains.THE_VALUE);
            }
            for (TypeOps.Declared declared :
                    own ? c.clauses.declared(named, data) : List.<TypeOps.Declared>of()) {
                Core stated = c.clauses.typed(declared.clause().expr(), named, data);
                if (stated == null) {
                    read = false;
                    notGathered.add(FieldDomains.THE_VALUE);
                    continue;
                }
                // Where this clause becomes a rule of the model something can be attributed to.
                // Everything below carries the origin as it is: what is written down here is read
                // back by a report, and a reader handed the clause reference instead would have to
                // decide for itself which of the rules that draw a line it was looking at.
                RuleRef.Invariant origin = new RuleRef.Invariant(Clause.Ref.of(declared));
                written.add(new Written(origin, stated));
                Predicates.Owed owed = c.predicates.obligations(stated, k, at, false);
                // And the reading that builds the numeric constraints, said by what it produced.
                // `value * 2 >= 4` is beyond the two readings below and is taken in here about the
                // position itself; `value * value >= 4` comes back about an atom standing for the
                // product, which is not the position and is not a reading of it.
                Predicates.subjectsIn(owed).forEach(spoken -> took.record(origin, spoken));
                read &= !owed.unreadable();
                k = c.predicates.assume(owed, k, Known.Held.OF_THE_VALUE);
            }
            // And what each field's own type says of it, at the field's own location. A depth of one
            // is already spent on the record, so this reaches the field's newtype and stops where the
            // seeding of a parameter would.
            for (Map.Entry<String, BindingId> field : bindings.entrySet()) {
                Type type = fields.get(field.getKey());
                if (type != null) {
                    // No depth limit here: this is the reading a boundary is derived from, and a
                    // rule the construction must satisfy is a rule wherever in the value it sits.
                    k = c.engine.seedAt(new Core.Read(field.getKey(), field.getValue(), type, NOWHERE),
                            data.newtype() ? FieldDomains.THE_VALUE : field.getKey(),
                            k, at, 1, Integer.MAX_VALUE, new HashSet<>(), gathering, reach);
                }
            }
        } catch (RuntimeException why) {
            gaveUp("seedFields " + named.name(), why);
            return Seeded.nothingRead();
        }
        Map<String, FactSubject> atoms = new LinkedHashMap<>();
        Map<String, Type> typeAt = new LinkedHashMap<>();
        Map<String, FactSubject> held = new LinkedHashMap<>();
        Map<String, FactSubject> keys = new LinkedHashMap<>();
        for (Map.Entry<String, BindingId> field : bindings.entrySet()) {
            Type type = fields.get(field.getKey());
            if (type != null) {
                // A newtype's value is the same location as the newtype, so it is at no path of its
                // own and its fields are the first step there is. Named `value`, every position of a
                // record inside a newtype was filed one step deeper than anything asks for.
                c.name(new Core.Read(field.getKey(), field.getValue(), type, NOWHERE),
                        data.newtype() ? "" : field.getKey(), type, at, symbols, 1,
                        atoms, typeAt, held, keys);
            }
        }
        // Which of the clauses place an edge, asked once the positions have names to be recognised
        // by.
        Reading reading = c.directsIn(written, at, atoms, keys, held, typeAt, took);
        // And which values each position is left, off the same clauses and at the same moment. What
        // reached this value is the walk's answer and is given to both readings; what each of them
        // makes of a clause is its own, so neither can widen the other's idea of what it was handed.
        Map<FactSubject, Type> positions = positions(atoms, keys, typeAt);
        // And what the same clauses say about which values each position may hold and where each
        // position stops, off the same list at the same moment. One reading in two languages and
        // not two readings: the connectives belong to the clause, so an alternative nothing can
        // satisfy is dropped by asking the whole of what is known about it.
        StatedByClauses stated = StatedByClauses.top();
        for (Written each : written) {
            // A reading of its own per clause, so what it says it adopted is this clause's and not
            // everything before it. Recorded per clause because that is the granularity a question
            // has: a clause the readings took in whole sat beside one they could not, and the
            // position-wide account said both had gone unread.
            StatedByClauses one = StatedByClauses
                    .readingOf(c.terms, at, positions, symbols).read(each.clause(), true);
            stated = stated.meet(one);
            one.adopted().forEach(position -> took.record(each.from(), position));
        }
        ConstraintState constraints = k.constraints()
                .taking(stated.values())
                .taking(stated.ordered());
        for (Map.Entry<String, Count> each : settled.entrySet()) {
            FactSubject atom = atoms.get(each.getKey());
            Type type = typeAt.get(each.getKey());
            if (atom == null || type == null) {
                continue;
            }
            constraints = constraints.taking(
                    NumericDomain.LinearForm.atom(atom)
                            .minus(NumericDomain.LinearForm.constant(each.getValue().at())),
                    NumericDomain.Rel.EQ,
                    Map.of(atom, c.terms.granularityOf(type)));
        }
        return new Seeded(constraints, atoms, keys, held, reading, took, read,
                Set.copyOf(notGathered));
    }

    /**
     * The atom each position under {@code value} is named by, keyed by the path it is reached at.
     *
     * <p>The walk {@link #seedAt} took, over the same reads, so a position the seeding put a bound on
     * is a position this can name. Two levels down as well as one: a clause on a record relates a
     * field of a field to something, and the bound that leaves on it is read at the path it sits at
     * rather than at the record it happens to be inside.
     *
     * <p>A name wrapped round a value is not a step of the path ({@link Location#isStep}), which is
     * the rule the rest of this already reads by: the atom of {@code w.value.n} <em>is</em> the atom
     * of {@code w.n}, so naming the position {@code w.value.n} files it under a path nothing asks
     * about. Counted as a step, a wrapper was where the walk stopped, and every position under one
     * went unnamed — so the clauses of a record inside a newtype reached the domain and nothing could
     * ask for what they left.
     */
    private void name(Core value, String path, Type type, Denotations at, Symbols symbols,
                      int depth, Map<String, FactSubject> atoms, Map<String, Type> typeAt,
                      Map<String, FactSubject> held, Map<String, FactSubject> keys) {
        // What the position is called, and the atom it is. Asked together, because where a position
        // is a number the domain carries the two are one identity read once — and this asks it of
        // every level of a chain, so reading it twice costs more than the chain is long.
        //
        // Both, because only some positions are numbers. An enumeration is ordered and carries no
        // atom, so a clause bounding one is recognised by what it is called and by nothing above it.
        Terms.Position position = terms.positionOf(value, at);
        FactSubject atom = position.atom();
        if (atom != null) {
            atoms.put(path, atom);
        }
        FactSubject key = position.key();
        if (key != null) {
            keys.put(path, key);
        }
        if (atom != null || key != null) {
            typeAt.put(path, type);
        }
        // And what a rule counting this position spoke about, which is not what the position is. A
        // list is no number and has no atom above; the count of it has one, and a reader asking how
        // much the position holds is asking about that one.
        FactSubject counted = terms.takenAtomOf(value, type, at);
        if (counted != null) {
            held.put(path, counted);
        }
        // Through the names, to the value that has the fields. Each is read at the path it is worn
        // under, since wearing a name is not being somewhere else. How far the names reach is
        // `TypeOps`' answer and not a second walk of its own: a declaration that wraps its own kind
        // ends that walk, and a copy of it here is a place the two could come to disagree.
        Core inner = value;
        Type worn = type;
        for (TypeOps.Layer layer : TypeOps.newtypeChain(type, symbols)) {
            Type under = TypeOps.fieldTypes(layer.data(), symbols).get("value");
            if (under == null) {
                break;
            }
            inner = new Core.FieldAccess(inner, "value", under, NOWHERE);
            worn = under;
        }
        if (depth > PathEngine.FIELDS_SEEDED || !(worn instanceof Type.Ref ref)
                || !(symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data) || data.newtype()) {
            return;
        }
        for (Map.Entry<String, Type> field : clauses.fieldsOf(data).entrySet()) {
            name(new Core.FieldAccess(inner, field.getKey(), field.getValue(), NOWHERE),
                    PathEngine.under(path, field.getKey()), field.getValue(), at, symbols, depth + 1,
                    atoms, typeAt, held, keys);
        }
    }

    /**
     * The type at each position of a value, keyed by what that position is called.
     *
     * <p>Every position that has a name, and not only the ones that are numbers. Which values a
     * boolean or an enumeration has is as much an answer as which values an integer has, and a
     * reading keyed by the numeric atoms alone had no word for the first two. Where a position has
     * both names — a number is called one thing by the interval algebra and another by everything
     * else — both are filed, since a clause reaching it may be recognised by either.
     */
    private static Map<FactSubject, Type> positions(Map<String, FactSubject> atoms, Map<String, FactSubject> keys,
                                             Map<String, Type> typeAt) {
        Map<FactSubject, Type> out = new LinkedHashMap<>();
        typeAt.forEach((path, type) -> {
            FactSubject key = keys.get(path);
            if (key != null) {
                out.put(key, type);
            }
            FactSubject atom = atoms.get(path);
            if (atom != null) {
                out.put(atom, type);
            }
        });
        return out;
    }

    /** A field of the value at {@code path}. The root of a newtype's own reading is the value it
     * wraps, which is at no path of its own, so its fields are the first step there is. */
    private static String under(String path, String field) {
        return path.isEmpty() ? field : path + "." + field;
    }

    /**
     * One end a clause places on one coordinate of a value, and the declaration that placed it.
     *
     * <p>Separate from the bounds a projection leaves, because placing an edge and taking one in are
     * separate acts (ADR-0090). {@code a < b} beside {@code b <= 10} leaves {@code a} stopping at 9
     * and places nothing on it: that 9 is where {@code b} stops, and a position whose only limit is
     * another position's is one the model draws no line through. Only what is here may be a line.
     *
     * @param path     where the coordinate sits, read from the value these are of
     * @param measured whether the coordinate is a count taken of the position rather than its value
     * @param from     the rule that placed it, which is what names the line. The clause and not
     *                 the declaration it is on: two clauses of one declaration placing an end at
     *                 one value are two rules a row could be owed to, and held as declarations
     *                 they came back as one
     */
    record Direct(String path, boolean measured, RuleRef.Invariant from,
                  InvariantBound bound) {}

    /** One clause reaching a value, rebased onto the positions of that value, and which clause it
     * is. */
    private record Written(RuleRef.Invariant from, Core clause) {}

    /**
     * Told what a walk over a value gathers, as it gathers it.
     *
     * <p>What it found and what it lost, because the second is not visible in the first. A clause
     * that states nothing the check can read is dropped before any reading sees it, and which
     * position it governed is what is not known about it — so a collector told only of the clauses
     * that arrived would take them for every clause there is, and answer for a declaration on the
     * strength of rules it never saw.
     */
    interface Gathering {

        /**
         * The clause {@code from}, rebased onto the positions of the value being read.
         *
         * @param spokenFor the positions the reading that builds the numeric constraints took it in
         *                  about, said by that reading. Handed over here rather than worked out
         *                  afterwards: what a reading adopted is the reading's to say, and a caller
         *                  deciding it from the clause's shape is guessing at another reader's
         *                  semantics
         */
        void gathered(RuleRef.Invariant from, Core clause, Set<FactSubject> spokenFor);

        /**
         * A rule of this value that reached no reading, either because it could not be stated or
         * because the walk did not go where it is written.
         *
         * <p>Which rule is not said, and there is nothing to say: a clause that could not be stated
         * is one whose position is exactly what is unknown about it, and a subtree that was not
         * entered holds rules nobody here has read. What a collector does with it is the same
         * either way.
         */
        void missed(String path);
    }

    /** A coordinate a clause reaching this value could be about. */
    private record Coordinate(String path, boolean measured, Carrier carrier) {}

    /**
     * What the clauses of one value place on its coordinates, and which declarations relate each of
     * them to something else.
     *
     * <p>The second is what says who took an edge in. A bound is moved by a clause comparing the
     * coordinate to another, and which declaration wrote that clause is not read off the value's own
     * name: the same relation can be written on the record, on a record inside it, or on a name
     * wrapped round either, and only the one that wrote it has anything to answer for.
     *
     * @param narrowers the declarations whose clauses compare each coordinate to something without
     *                  placing an end on it, outermost first
     * @param raised    what each clause reaching this value raises, keyed on the rule it is.
     *                  Beside the ends rather than derived from them: a clause that placed no end
     *                  may have raised a question all the same, and a clause that placed one raised
     *                  more than the line. Nothing here says whether anything answered
     */
    record Reading(List<Direct> directs, Map<String, List<TypeSymbol>> narrowers,
                   Map<RuleRef, Required> raised) {}

    private Reading directsIn(List<Written> stated, Denotations at,
                                   Map<String, FactSubject> atoms, Map<String, FactSubject> keys,
                                   Map<String, FactSubject> held, Map<String, Type> typeAt,
                                   ReadingEvidence took) {
        Map<FactSubject, Coordinate> byName = new LinkedHashMap<>();
        keys.forEach((path, key) -> {
            Carrier carrier = Carrier.ofValue(typeAt.get(path), symbols);
            if (carrier != null) {
                byName.put(key, new Coordinate(path, false, carrier));
                FactSubject atom = atoms.get(path);
                if (atom != null) {
                    byName.put(atom, new Coordinate(path, false, carrier));
                }
            }
        });
        // A count is a whole number whatever it counts, so nothing about the container decides how
        // its sizes are spaced.
        held.forEach((path, atom) -> byName.put(atom, new Coordinate(path, true, Carrier.WHOLE)));
        List<Direct> out = new ArrayList<>();
        Map<String, List<TypeSymbol>> narrowers = new LinkedHashMap<>();
        Map<RuleRef, Required> raised = new LinkedHashMap<>();
        stated.forEach(each ->
                direct(each.clause(), each.from(), at, byName, out, narrowers, raised, took,
                        typeAt));
        // Insertion order, kept: `Map.copyOf` iterates in an order salted once per JVM run, and
        // what a report prints for a position is these in the order the declaration writes them.
        return new Reading(List.copyOf(out), Map.copyOf(narrowers),
                java.util.Collections.unmodifiableMap(new LinkedHashMap<>(raised)));
    }

    /** What {@code clause} raises, taken together with whatever its other conjuncts raised. */
    private static void raises(Map<RuleRef, Required> into, RuleRef.Invariant rule,
                               ClauseStates states) {
        into.merge(rule, Required.ofInvariant(states), Required::and);
    }

    /**
     * What one part of {@code rule} raises, and — where this reading made nothing of it — whether
     * anything else took that part in.
     *
     * <p>Asked of the part and not of the clause. A conjunction is one rule the author wrote and is
     * read a conjunct at a time; evidence gathered for the whole answers a clause half of which
     * nothing read on the strength of the half that was, which is how `value >= 1 && value * value
     * >= 4` came back with nothing to say while the same two rules written apart were reported.
     */
    private void settle(Core part, RuleRef.Invariant rule, ClauseStates states,
                        Denotations at,
                        Map<FactSubject, Coordinate> byName, Map<RuleRef, Required> raised,
                        ReadingEvidence took, Map<String, Type> typeAt) {
        raises(raised, rule, states);
        if (!(states instanceof ClauseStates.SomethingElse other)) {
            return;
        }
        // The positions this part is about, by every name each answers to, since a reading files a
        // clause under whichever name it recognised.
        Set<FactSubject> about = new LinkedHashSet<>();
        for (Map.Entry<FactSubject, Coordinate> each : byName.entrySet()) {
            if (other.positions().contains(Owed.Subject.at(each.getValue().path()))) {
                about.add(each.getKey());
            }
        }
        if (about.isEmpty()) {
            return;
        }
        Map<FactSubject, Type> positions = new LinkedHashMap<>();
        byName.forEach((name, where) -> {
            Type type = typeAt.get(where.path());
            if (type != null) {
                positions.put(name, type);
            }
        });
        Set<FactSubject> here = StatedByClauses.adoptedIn(part, terms, at, positions, symbols);
        Set<FactSubject> constrained =
                Predicates.subjectsIn(predicates.obligations(part, Known.top(), at, false));
        Set<FactSubject> standing = new LinkedHashSet<>();
        for (FactSubject name : about) {
            if (!here.contains(name) && !constrained.contains(name)) {
                standing.add(name);
            }
        }
        if (!standing.isEmpty()) {
            took.leftStanding(rule, standing);
        }
    }

    /**
     * {@code clause}'s ends and what it relates, taking a conjunction one conjunct at a time as an
     * invariant is.
     *
     * <p>Both answers from one reading of the clause. A comparison either places an end on a
     * coordinate or relates one to something else, and which of the two it did is the same question
     * asked once — read apart, the second would be a walk that had to agree with this one about which
     * comparisons it had already accounted for.
     */
    private void direct(Core clause, RuleRef.Invariant from, Denotations at,
                        Map<FactSubject, Coordinate> byName, List<Direct> out,
                        Map<String, List<TypeSymbol>> narrowers,
                        Map<RuleRef, Required> raised, ReadingEvidence took,
                        Map<String, Type> typeAt) {
        if (!(clause instanceof Core.Binary bin)) {
            settle(clause, from, states(clause, at, byName), at, byName, raised, took, typeAt);
            return;
        }
        if (bin.op() == Hir.BinOp.AND) {
            // One rule the author wrote, so what it raises is what its conjuncts raise together.
            direct(bin.left(), from, at, byName, out, narrowers, raised, took, typeAt);
            direct(bin.right(), from, at, byName, out, narrowers, raised, took, typeAt);
            return;
        }
        if (!InvariantBound.ordering(bin.op()) && bin.op() != Hir.BinOp.EQ) {
            settle(bin, from, states(bin, at, byName), at, byName, raised, took, typeAt);
            return;
        }
        // The coordinate-bearing side read as the left one, as `0 <= value` says what `value >= 0`
        // says.
        Coordinate found = byName.get(nameOf(bin.left(), at));
        Core bound = bin.right();
        Hir.BinOp op = bin.op();
        if (found == null) {
            found = byName.get(nameOf(bin.right(), at));
            bound = bin.left();
            op = InvariantBound.flipped(op);
        }
        // An end where the other side is a constant, and a relation everywhere else. Which it is
        // cannot be asked of the other side's name: what a clause compares a coordinate to may be a
        // position deeper than this names, or arithmetic over several, and neither is a number an
        // edge can be put at. So the end is attempted and what fails to be one may have moved one.
        // A line is placed only where an end was read. A rule stating an end past the last value of
        // the order places none — there is no value to draw a line at — and it is not a relation
        // either: what it compares the coordinate to is a constant this read perfectly. So it falls
        // out here rather than being filed as a clause that could have moved an edge.
        InvariantBound.Read end = found == null || !InvariantBound.ordering(op)
                ? new InvariantBound.Read.NoEnd()
                : InvariantBound.at(op, Terms.asWrittenValue(bound), found.carrier());
        Coordinate about = found;
        settle(bin, from, switch (end) {
            // Two questions about two subjects: which values may stand at the position, and a line
            // on whichever number the rule measured it by.
            case InvariantBound.Read.AnEnd _ -> new ClauseStates.AnEnd(
                    Owed.Subject.at(about.path()),
                    new Owed.Subject(about.path(), about.measured()));
            // A rule this read perfectly, and what it says is that no value stands here. No line
            // follows: there is no value for a row to be written at.
            case InvariantBound.Read.PastWhereTheOrderStops _ ->
                    new ClauseStates.NoValueAtAll(Owed.Subject.at(about.path()));
            case InvariantBound.Read.NoEnd _ -> states(bin, at, byName);
        }, at, byName, raised, took, typeAt);
        if (end instanceof InvariantBound.Read.NoEnd) {
            // The declaration and not the clause. Which declaration took an edge in is what ADR-0090
            // names beside a line, and what a reader is sent to look at is the declaration holding
            // the relation.
            relating(clause, from.clause().id().declaredOn(), at, byName, narrowers);
            return;
        }
        if (end instanceof InvariantBound.Read.AnEnd placed) {
            out.add(new Direct(found.path(), found.measured(), from, placed.bound()));
        }
    }


    /**
     * What a comparison that placed no end is about.
     *
     * <p>Asked of the shape and not of what the reading managed. A rule relating two coordinates was
     * read to the end — both sides were recognised — and raises no question about one position; a
     * rule this made nothing of raises the same question every other rule about a position's values
     * raises, and is answered or not by whichever reading could take it in.
     */
    private ClauseStates states(Core clause, Denotations at,
                                Map<FactSubject, Coordinate> byName) {
        if (Relates.twoPositions(clause, e -> {
            FactSubject named = nameOf(e, at);
            return named != null && byName.containsKey(named) ? named : null;
        })) {
            return new ClauseStates.ARelation();
        }
        List<Owed.Subject> found = new ArrayList<>();
        namedIn(clause, at, byName, found);
        return ClauseStates.SomethingElse.naming(found);
    }

    /**
     * The positions {@code e} names, which is what a clause this made nothing of can cost.
     *
     * <p>It cannot cost a position it does not name: nothing here relates one position to another —
     * that is the arm above — so a rule narrowing a position names it. The same walk
     * {@link #relating} makes, and for the same reason: a coordinate names itself, and nothing under
     * it is a coordinate of its own.
     */
    private void namedIn(Core e, Denotations at, Map<FactSubject, Coordinate> byName,
                         List<Owed.Subject> out) {
        FactSubject named = nameOf(e, at);
        Coordinate here = named == null ? null : byName.get(named);
        if (here != null) {
            Owed.Subject where = Owed.Subject.at(here.path());
            if (!out.contains(where)) {
                out.add(where);
            }
            return;
        }
        Core.forEachChild(e, child -> namedIn(child, at, byName, out));
    }

    /**
     * Files {@code from} under every coordinate this comparison could carry a bound to.
     *
     * <p>Every coordinate it names and not only the two it compares: a bound reaches a position
     * along the differences, so a clause reading {@code a} is a way {@code a}'s edge can have been
     * moved even where the number came from somewhere further off.
     */
    private void relating(Core clause, TypeSymbol from, Denotations at,
                          Map<FactSubject, Coordinate> byName,
                          Map<String, List<TypeSymbol>> narrowers) {
        FactSubject named = nameOf(clause, at);
        Coordinate found = named == null ? null : byName.get(named);
        if (found != null) {
            List<TypeSymbol> had = narrowers.computeIfAbsent(found.path(), _ -> new ArrayList<>());
            if (!had.contains(from)) {
                had.add(from);
            }
            return;   // a coordinate names itself and nothing under it is a coordinate of its own
        }
        Core.forEachChild(clause, child -> relating(child, from, at, byName, narrowers));
    }

    /**
     * What {@code e} is called where a coordinate is looked up.
     *
     * <p>{@link Terms#atomOf} first, which is what a size call is known by: the shape a size keys as
     * is held under a name of its own, and the shape itself is not that name. Read off the shape,
     * every rule counting a field looked like a rule about nothing.
     *
     * <p>Then what the position is called, for the positions that are ordered and are not numbers. An
     * enumeration has no atom and a clause can still say where its values stop.
     */
    private FactSubject nameOf(Core e, Denotations at) {
        return terms.subjectOf(e, at);
    }

    /**
     * Whether every rule that can refuse a value of {@code data} was read as a bound.
     *
     * <p>{@link ClauseDischarge.Kind#DERIVABLE} is the same classification a construction is judged
     * by, asked here of the declaration rather than of a site. A clause that is only nameable — a
     * pattern, a membership — narrows no bound, and a clause outside the fragment narrows none
     * either; both leave a way the record refuses a value that the bounds do not express. The same
     * reach the seeding has, so what this classifies is what that took in.
     *
     * <p>Asked over the values a construction has to produce, which is not the depth a report takes a
     * value apart to. {@code FIELDS_SEEDED} and {@code MAX_DEPTH} are limits on how far a measurement
     * is worth carrying; a rule four records down refuses the outermost construction exactly as one
     * on its own fields does, so a bound at the top is promised by nothing while that rule is unread.
     *
     * <p>Down the required chain only. A field that is optional or a collection can be absent or
     * empty, so a rule inside it is a rule about a value the construction need not make. A type
     * already met is not entered again, which is what stops a record that holds itself.
     */
    static boolean everyRuleRead(TypeSymbol named, Hir.Data data, Symbols symbols) {
        return everyRuleRead(named, data, symbols, new HashSet<>());
    }

    /**
     * Whether every reading of {@code clause} is a bound.
     *
     * <p>Nothing here is shown to anybody, so nothing here is placed: this asks what the check made
     * of a clause and not where to say it, and a reader with no author in front of it has no position
     * to be right or wrong about. What it reads is the clause as this checker holds it, which is the
     * representation the rest of this walk is written against.
     */
    private static boolean readOnlyAsBounds(Hir.Expr clause, TypeSymbol named, Hir.Data data,
                                            Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols, Map.of());
        Core stated = c.typed(read -> c.clauses.typed(read, named, data), clause, data.name());
        for (ClauseDischarge.Kind read : c.kindsRead(stated,
                Denotations.none().locations(c.clauses.bindingsOf(named, data).values(),
                        c.terms::placeSubject, c.terms::placeTerm),
                data.name())) {
            if (read != ClauseDischarge.Kind.DERIVABLE) {
                return false;
            }
        }
        return true;
    }

    private static boolean everyRuleRead(TypeSymbol named, Hir.Data data, Symbols symbols,
                                         Set<TypeSymbol> seen) {
        if (!seen.add(named)) {
            return true;
        }
        if (data.newtype()) {
            if (!everyRuleBecameABound(named, data, symbols)) {
                return false;
            }
        } else {
            for (Hir.InvariantClause clause : TypeOps.effectiveInvariants(data, symbols)) {
                // Every reading of it, and not one of them: a clause read as a bound and as
                // something else besides is a clause part of which no bound expresses.
                if (!readOnlyAsBounds(clause.expr(), named, data, symbols)) {
                    return false;
                }
            }
        }
        for (Type type : TypeOps.fieldTypes(data, symbols).values()) {
            if (type instanceof Type.Ref ref && symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data inner
                    && !everyRuleRead(ref.name(), inner, symbols, seen)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether every rule on a newtype became one of the constraints its bounds are read from.
     *
     * <p>The same reader, so the same answer: a conjunct that gave the position a bound was read, and
     * one that gave none — {@code isOdd(value)} beside {@code value >= 0} — is a way the type refuses
     * a value that the bounds do not express.
     *
     * <p>Which reader that is depends on what the value is carried as. An ordered value's range comes
     * from the comparison itself and is read by the one interpreter that reads every ordered rule;
     * anything else — a pattern, a size, a quantifier — is read as the runtime check it becomes,
     * which is the only reading of those there is.
     *
     * <p>The carrier decides which, and it is asked of the type rather than derived from a second
     * list of what counts as a number. Read off such a list, a {@code Date} newtype's bound went to
     * the runtime-check reader, which has no word for a date comparison — so a rule the interval
     * algebra reads as a bound came back unreadable, and every boundary of the record it sat in lost
     * its writability with it.
     *
     * <p>One conjunct at a time, and all of them. A clause is split to its leaves first, so a leaf is
     * either an ordered bound whole or not one at all; a rule of another shape beside a bound is a
     * way the type refuses a value that the bounds do not express, and saying the bounds are the
     * whole story would offer a row nothing can build.
     */
    private static boolean everyRuleBecameABound(TypeSymbol named, Hir.Data data, Symbols symbols) {
        Carrier carrier = Carrier.ofValue(Type.ref(named), symbols);
        Type base = TypeOps.fieldTypes(data, symbols).get("value");
        // Every name the value wears, read against what it is carried as. Asking only the outermost
        // one leaves a rule a layer down unaccounted for, and reading it against the type that layer
        // declares rather than against what carries the value makes every such rule unreadable.
        for (TypeOps.Layer layer : TypeOps.newtypeChain(Type.ref(named), symbols)) {
            for (Hir.InvariantClause clause : TypeOps.effectiveInvariants(layer.data(), symbols)) {
                for (Hir.Expr each : ClauseHelpers.conjunctsOf(clause.expr())) {
                    // A `String` is the one type two measures answer for — its own order, and the
                    // length of it — so a rule about either is a rule that was read, and both are
                    // asked. Every other carrier is measured one way, and asking the second reader
                    // as well would call a rule read that no measure took in.
                    boolean read = carrier instanceof Carrier.Text
                            ? readAsABound(each, carrier)
                                    || souther.compiler.codegen.InvariantConstraints
                                            .of(each, base).isPresent()
                            : carrier != null ? readAsABound(each, carrier)
                                    : souther.compiler.codegen.InvariantConstraints
                                            .of(each, base).isPresent();
                    if (!read) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /**
     * Whether the ordered reading took {@code clause} in, however it turned out.
     *
     * <p>A rule stating an end past the last value of the order was read: what it says is that
     * nothing satisfies it, which is as much an account of the clause as an end is. Counted as
     * unread, it would say the bounds are not the whole story about a declaration whose rules this
     * understood completely.
     */
    private static boolean readAsABound(Hir.Expr clause, Carrier carrier) {
        return !(InvariantBound.of(clause, carrier) instanceof InvariantBound.Read.NoEnd);
    }

    /** A position read from no source, for the reads this makes to stand at. */
    private static final SourcePos NOWHERE = new SourcePos(0, 0);

    /**
     * Analyzes one behavior body against the bindings its inputs are. Nothing the body is throws:
     * a walk that cannot get through one comes back {@code ABANDONED}. {@link Terms.OneTermTwoKinds}
     * is not something the body is and is not caught ({@link #gaveUp}). A {@code null} body is one
     * the analysis representation could not be built or typed for, and is not analyzed at all.
     */
    static Findings analyze(Core body, Map<TypeSymbol, List<Hir.InvariantClause>> invariants,
                            Map<ValueName.Behavior, StatedContract> contracts,
                            Scope params, Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols, invariants, contracts);
        if (body == null) {
            return new Findings(c.errors, c.warnings, Status.ABANDONED);
        }
        try {
            Entered in = new Entered(Known.top(), Denotations.none());
            for (Map.Entry<BindingId, Scope.Binding> p : params.bindings().entrySet()) {
                in = c.enter(new Core.Read(p.getValue().name(), p.getKey(), p.getValue().type(),
                        body.pos()), in.known(), in.at());
            }
            c.entering(body, in.known(), in.at(), 1);
        } catch (RuntimeException why) {
            // fail-open: the run-time invariant check remains the backstop
            gaveUp("analyze", why);
            return new Findings(c.errors, c.warnings, Status.ABANDONED);
        }
        return new Findings(c.errors, c.warnings, Status.COMPLETE);
    }

    /**
     * Records an analysis that fell over, for a test in this package to read.
     *
     * <p>Every place this check swallows a failure comes through here, so what must not be swallowed
     * is refused in one place. A shape the walk has no rule for is what fail-open is for: the
     * run-time check stands for the clause, and reporting the walk's limit as the author's problem is
     * what the policy avoids. {@link Terms.OneTermTwoKinds} is not that. It says this check called two
     * values one value, and what it would produce if caught is a behavior with no findings — which
     * is exactly what a behavior whose invariants all discharge produces.
     *
     * <p>{@link souther.compiler.diag.DiagnosticPlace.NotOnePlace} and {@link Clause.NotOneClause} are not that either, for
     * the same reason. One says a place this check was about to send a reader to runs between two
     * files; the other says two readings of one clause disagree about what the declaration says.
     * Both are this compiler's model contradicting itself, which is a different thing from this
     * compiler not being able to follow a program.
     */
    static void gaveUp(String where, RuntimeException why) {
        // Asked of what the failure is and not of which ones this has met. A list here is a copy of
        // the types that carry the distinction, and a new way for the check to disagree with itself
        // would go on being reported as an ordinary limit with nothing failing while it did.
        if (why instanceof souther.compiler.diag.TheCompilerDisagreesWithItself) {
            throw why;
        }
        List<GaveUp> watching = GAVE_UP;
        if (watching != null) {
            watching.add(new GaveUp(where, why));
        }
    }

    // --- the walk ------------------------------------------------------------------------------

    /**
     * Reads what the answers under {@code e} guarantee, and walks {@code e} over it — which is
     * {@link #walk}'s one requirement, met here.
     *
     * <p>How far the reading runs is {@link PathEngine#answering}'s question, and it stops where
     * reading ahead would be wrong rather than merely early: at a branch, at a block, and at a
     * binding's body, each of which is read with something further settled. Those are the places
     * that come back through here, so a call is read once, where it stands, and not once for every
     * node standing over it — read again from a descendant it lands on the subjects it already
     * holds, and costs the cost of a body over again at every node of it (#826).
     *
     * <p>Nothing reaches what this was handed, so there is nothing under it to be about. Asked here
     * and again of the reading, because the reading is itself a place the conditions can come to
     * contradict.
     */
    private void entering(Core e, Known given, Denotations at, int cost) {
        entering(e, e, given, at, cost);
    }

    /**
     * The same, where {@code given} already meets that requirement over part of {@code e}:
     * {@code unread} is the part it does not, or null where there is no such part.
     *
     * <p>Which is what a walk that rebuilds an expression is owed. Entering a binding that stood
     * inside a value walks the expression with the binding's body put where the binding was, and
     * opening a case split a value is handed walks it once with each arm put there. Either way
     * the tree is the whole expression — what the source would have written without the helper or
     * the split, and what the rest of this walk reads — while everything but the part put in
     * was read where the region was entered.
     *
     * <p>Reading that part again would land on the subjects it already holds, under a denotation it
     * cannot tell apart: a binder an expansion introduced was written around its own body, and the
     * binders a split stands inside scope over the split and no further, so nothing
     * standing beside either was written where it could name them.
     *
     * <p>And nothing is unread where what was put in went somewhere the reading had already stopped.
     * The requirement is over what the reading reaches from here, which is not past a region
     * boundary; a branch put in beyond one is read by the region that owns it, when the walk arrives
     * there. Which of the two a split is, is what {@link SplitSite#read} answers.
     */
    private void entering(Core e, Core unread, Known given, Denotations at, int cost) {
        if (given.reachesNothing()) {
            return;
        }
        walk(e, unread == null ? given : engine.answering(unread, given, at), at, cost);
    }

    /**
     * One step of a region, over facts that already hold of it.
     *
     * <p>What every step is handed, and the one thing every caller owes: {@code k} holds what
     * {@link PathEngine#answering} derives over {@code e}, as far as that reading goes from
     * {@code e}. It is owed because a construction is judged at its own step while the answers it is
     * built from stand underneath it — judged against {@code k} alone, it would be judged before the
     * value it was handed had said anything. {@link #entering} is where it is met.
     *
     * <p>Every descent from here that is not a region of its own hands {@code k} on unchanged, and
     * may: a reading that covers this step covers a child exactly as far. So a step that reaches
     * nothing stands in a region that reached nothing, and that was settled where it was entered.
     */
    private void walk(Core e, Known k, Denotations at, int cost) {
        if (k.reachesNothing()) {
            return;
        }
        Core.LetIn standing = bindingInValueIn(e);
        if (standing != null) {
            // A call this analysis expanded is a binding holding what it was given, and where that
            // binding stands inside a value — under a field read, under one side of a comparison —
            // it is not one the walk steps into. What it holds is then a name nothing has entered,
            // which denotes nothing: the chain off it names no location, and a construction over a
            // term nothing can name is owed no clause at all. Entered here, what is left is the tree
            // the source would have written with a `let`, which is the tree the rest of this walk
            // already reads — so a construction moved into a helper reads the terms its caller's
            // guards settled, which is what the expansion is for.
            if (!(standing.value() instanceof Core.Block)) {
                walk(standing.value(), k, at, cost);
            }
            Entered in = bindLet(standing, k, at);
            entering(without(e, Set.of(standing), standing.body()), standing.body(), in.known(),
                    in.at(), cost);
            return;
        }
        SplitSite site = splitValueIn(e);
        Split split = site == null ? null : splitOf(site.split());
        if (split != null && opens(cost, split.arms().size())) {
            // A case split in a value position is one of its arms, and which one is decided by what
            // it asks — an `if` by its condition, a `match` by which case the scrutinee is. So this
            // is read once with each arm standing there, under what choosing that arm settles, and
            // what the readings find is said once. Every place such a value can be given — to a
            // field, to a name, to a guard — is this one place.
            Core value = site.split();
            // Everything about the split is read where it stands, which is inside every binder on the
            // way down to it and not at the outer place the reading is decided on: what it asks, and
            // what the asking's own subtree is. Read at the outer place, what it asks names binders
            // nothing has entered, which denote nothing — it would settle nothing, and a construction
            // written inside it would be one nothing can be said of.
            Entered inside = scopeOf(site, k, at);
            Known within = inside.known();
            Denotations there = inside.at();
            // What the split asks is read here only where the reading stopped short of it. Reached
            // from where the region was entered, it stands in `within` already.
            if (site.read()) {
                walk(split.asked(), within, there, cost);
            } else {
                entering(split.asked(), within, there, cost);
            }
            Set<Core> alike = sameSplit(e, value, there);
            // The readings start from where the split stood, not from outside it. The tree each is
            // given still holds those binders and walks into them again, which is why entering one
            // already entered is nothing: a second transition would forget what the arm settled.
            // Only the arm is unread. Everything beside the split was read where this region was
            // entered and stands in `within`, and the readings differ in what choosing an arm settles
            // rather than in what stands outside it. Where the reading stopped short of the split,
            // nothing here is: the arm stands where the region that owns it reads it, and this walk
            // reaches that region on its way down.
            List<Map<Occurrence, Reported>> readings = new ArrayList<>();
            for (Arm arm : split.arms()) {
                Entered under = arm.under().entering(within, there);
                readings.add(reading(without(e, alike, arm.body()),
                        site.read() ? arm.body() : null,
                        under.known(), under.at(), cost * split.arms().size()));
            }
            say(readings);
            return;
        }
        switch (e) {
            case Core.Construct made -> {
                judge(made, k, at, false);
                Core.forEachChild(made, child -> walk(child, k, at, cost));
            }
            case Core.If iff -> {
                walk(iff.cond(), k, at, cost);
                entering(iff.then(), predicates.assumeCond(iff.cond(), k, at, true).known(), at,
                        cost);
                entering(iff.els(), predicates.assumeCond(iff.cond(), k, at, false).known(), at,
                        cost);
            }
            case Core.IfConstructed ic -> {
                // The attempt's own construction cannot abort — a failing invariant is the else
                // branch — so it is checked for a decided violation and never warned about as a
                // possible one. Its field values are walked on their own so a construction nested
                // inside an argument is still an ordinary, aborting one.
                judge(ic.construct(), k, at, true);
                Core.forEachChild(ic.construct(), child -> walk(child, k, at, cost));
                // Reaching `then` is the construction having held, so the binding carries the type's
                // invariant exactly as an input of that type does — which is a location, and not the
                // construction read again. What the construction denotes is what the check could say
                // of the attempt, and an attempt is written where it could not say enough: an
                // expression it cannot name denotes nothing, and inheriting that would drop the one
                // thing reaching this branch established.
                Entered in = engine.enteringBuilt(ic, k, at);
                entering(ic.then(), in.known(), in.at(), cost);
                // Each departure stands where the invariant did not hold, and nothing was built
                // there, so none of them is seeded with anything the attempt would have guaranteed.
                ic.els().forEach(arm -> entering(arm.body(), k, at, cost));
            }
            case Core.LetIn li -> {
                // A closure is read where it is applied: what its parameter holds is decided there,
                // and reading it here would read every construction in it with the element unknown.
                if (!(li.value() instanceof Core.Block)) {
                    walk(li.value(), k, at, cost);
                }
                Entered in = bindLet(li, k, at);
                entering(li.body(), in.known(), in.at(), cost);
            }
            case Core.Match m -> {
                walk(m.scrutinee(), k, at, cost);
                for (Core.Case c : m.cases()) {
                    // A sum has no fields of its own, so the scrutinee is not a location any clause
                    // could have named — the case's value names only itself. What the arm binds is a
                    // value of the case's type, reached only here, so it is a location this arm
                    // introduces and it carries what that type guarantees.
                    // The scrutinee travels with the arm: what a caller may assume of an answer is
                    // decided by which behavior answered and which case this arm opened, and the
                    // first of those is a question about what is being matched.
                    Entered in = engine.enteringArm(c, m.scrutinee(), k, at);
                    entering(c.body(), in.known(), in.at(), cost);
                }
            }
            case Core.PreservedCall call -> walkCall(call, k, at, cost);
            // A closure the reading stopped at, reached as a value like any other. What its body
            // answers is decided where the closure is applied, so nothing out here read it, and it
            // is a region of its own however it was arrived at.
            case Core.Block block -> Core.forEachChild(block, b -> entering(b, k, at, cost));
            default -> Core.forEachChild(e, child -> walk(child, k, at, cost));
        }
    }

    /** Walks a call the representation kept standing, entering a combinator closure's parameters as
     * the locations the application introduces — the element at the container's element type, and
     * every other at what the closure was typed with — so a construction inside the closure is
     * analyzed rather than left opaque. A closure is where its parameters are values, which is here
     * and not where the block is written. */
    private void walkCall(Core.PreservedCall call, Known k, Denotations at, int cost) {
        Handed handed = Combinators.handedTo(call, at);
        for (Core arg : call.args()) {
            // The closure is asked by identity: a call may write one expression twice, and only the
            // argument the operation applies is the one an element arrives in.
            if (handed == null || arg != handed.closure()) {
                walk(arg, k, at, cost);
                continue;
            }
            Core container = handed.container();
            Type elem = Terms.elementType(container.type());
            // The container is read where the call is written, so what is known of its elements
            // is looked up before the closure's parameter stands for anything.
            List<Quantified> relations = predicates.elementRelations(container, k, at);
            Core.Read element = Terms.read(handed.element(), elem, handed.step().pos());
            // an element of a container is not a location the body can otherwise name
            Entered in = enter(element, k, at);   // the element carries its type's invariant
            // What a fold hands its step beside the element is a value of the type it was seeded
            // with, built through that type's checked constructor like any other — so it carries
            // that type's invariant, and the accumulator is not the one binding that has to give
            // its newtype up to be reasoned about.
            in = enterOthers(handed, in);
            Known k2 = in.known();
            for (Quantified q : relations) {
                k2 = predicates.instantiate(q, element, k2, in.at());
            }
            entering(handed.step().body(), k2, in.at(), cost);
        }
    }

    /** {@code in} with the closure's parameters other than the element entered at the types the
     * closure was typed with. A closure typed as anything but a function hands its parameters
     * nothing this can name, and they stay out. */
    private Entered enterOthers(Handed handed, Entered in) {
        if (!(handed.step().type() instanceof Type.FnOf fn)) {
            return in;
        }
        List<Hir.Binder> params = handed.step().params();
        Entered out = in;
        for (int i = 0; i < params.size() && i < fn.params().size(); i++) {
            if (params.get(i) == handed.element()) {
                continue;
            }
            // A call the representation kept standing was applied to a signature that accepted it,
            // so its closure is typed. Answering an untyped parameter with the element's type would
            // seed another type's invariant at a place this cannot read, so it is not answered.
            Type given = fn.params().get(i);
            if (given == null) {
                throw new IllegalStateException("a closure a preserved call applies has an untyped"
                        + " parameter, so what it is handed cannot be said");
            }
            out = enter(Terms.read(params.get(i), given, handed.step().pos()), out.known(), out.at());
        }
        return out;
    }

    // --- the discharge check -------------------------------------------------------------------

    /**
     * What this check says about one construction. Every value a body makes is one of these, so
     * there is nothing to recognise here: a construction was settled where the tree was built, and
     * what it builds and what each of its fields is given came with it.
     */
    private void judge(Core.Construct made, Known k, Denotations at, boolean attempted) {
        if (symbols.declarations().declaration(made.typeName().key()) instanceof Hir.Data type) {
            report(made, type, made.pos(), attempted, verdictOf(made, type, k, at));
        }
    }

    /**
     * The verdict for one construction, over what each field is being given. A case split never
     * reaches here: the walk opens it before anything is checked, so what a field is given is a
     * value and not a choice of arms.
     */
    private Judgment verdictOf(Core.Construct nd, Hir.Data type, Known k, Denotations at) {
        Map<String, BindingId> fields = clauses.bindingsOf(nd.typeName(), type);
        Map<BindingId, Core> given = new HashMap<>();
        for (Core.FieldValue fv : nd.values()) {
            BindingId field = fields.get(fv.field());
            if (field == null) {
                continue;
            }
            // A name given a value written out hands over that value: the clause folds over what
            // was written, wherever the writing was done.
            Core written = terms.writtenValue(fv.value(), at);
            given.put(field, written != null ? written : fv.value());
        }
        return verdictOf(nd.typeName(), type, given, k, at, !constantlyBuilt(type, nd));
    }

    /** Which of the values a construction hands over is not one a clause may be read against
     * ({@link Terms#reportableSite}) — by identity, since it is these very values that stand in the clause. */
    private Set<Core> unnamed(Collection<Core> given, Known k, Denotations at) {
        Set<Core> out = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Core value : given) {
            if (terms.reportableSite(value, at, k) == null) {
                out.add(value);
            }
        }
        return out;
    }

    /**
     * How a construction came out. A construction is checked before it is reported so that one
     * written over a case split can be checked on each arm and answered once — which of the arms'
     * values it is is not decided here, so what holds of the construction is what holds of all.
     */
    enum Verdict {
        /** Every clause is discharged. */
        PROVED,
        /** A clause names something the check cannot read at this construction, and no clause is
         * unproven: nothing is owed here because nothing could be asked. Silent, as a discharge is,
         * and not the same thing — the run-time check is what stands for the clause, and an author
         * who reads the silence as a proof is reading something that was never attempted. */
        UNREPRESENTABLE,
        /** A clause is expressible and unproven: the construction may abort. */
        UNKNOWN,
        /** A clause the reading without the path's assumptions already refutes, so the invariant
         * fails wherever the construction is written. */
        REFUTED_ALONE,
        /** A clause the full reading refutes and that reading does not. Something known here beyond
         * the values themselves settled it; which of the things known here is not asked, so this
         * does not say a condition on the path was one of them. */
        REFUTED_NOT_ALONE;

        boolean refuted() {
            return this == REFUTED_ALONE || this == REFUTED_NOT_ALONE;
        }

        /** Whether the reading found nothing that may fail: every clause it could read is
         * discharged. Not the same question as whether anything is reported — what is reported is
         * settled at {@link #report}, and this is what the two readings of one construction are
         * combined by. */
        boolean holds() {
            return this == PROVED || this == UNREPRESENTABLE;
        }

        /**
         * What holds of a value that is one of two. It is discharged where both are, and it is proven
         * to fail only where both fail — a construction one branch satisfies does not definitely
         * violate, whichever branch is taken. Everything else is possible and unproven.
         *
         * <p>Where both fail and only one of them fails on the values alone, the two together are
         * said not to: what is claimed of the construction is what the weaker of the two readings
         * supports. The other direction is the clauses of one invariant, which are conjoined rather
         * than alternative and are combined at {@link #verdictOf} the other way round.
         *
         * <p>A branch nothing reaches finds nothing to combine: {@link #reading} answers it with no
         * findings at all, and a position only one branch found is read as discharged on the other.
         */
        static Verdict of(Verdict a, Verdict b) {
            if (a == b) {
                return a;
            }
            if (a.refuted() && b.refuted()) {
                return REFUTED_NOT_ALONE;
            }
            // Neither reading found anything that may fail, and they are not the same reading: one
            // discharged the invariant and the other could not read it. So neither does this, and
            // what it is not is the invariant proven of both.
            return a.holds() && b.holds() ? UNREPRESENTABLE : UNKNOWN;
        }
    }

    /** The discharge verdict for a construction of {@code type} whose fields are being given
     * {@code given}. */
    private Judgment verdictOf(TypeSymbol named, Hir.Data type, Map<BindingId, Core> given, Known k,
                               Denotations at, boolean decidesFalse) {
        // What the construction hands over that no clause may be read against. A clause naming one of
        // them is left to the run-time check, and one that is decided outright is still decided: what
        // cannot be guarded is not the same as what cannot be computed.
        Set<Core> unnamed = unnamed(given.values(), k, at);
        List<Owing> owed = new ArrayList<>();
        // Every clause that was read, in the order it was declared, and what was proved about it.
        // Every clause, whether or not the author named it: what a diagnostic can say about one is
        // the clause's to answer, and a clause left out of here because it could not be named is a
        // clause nothing downstream can point at either. One entry per clause, so no clause can be
        // on two sides of this at once.
        SequencedMap<Clause.Id, Judged> found = new LinkedHashMap<>();
        boolean refutedAlone = false;
        // Whether any clause is unsettled, which is not the same as whether any named one is: a
        // clause MAY be written without a name, and one that was is still a clause the guards did
        // not establish. Reading the answer off the names alone made an unnamed clause discharge.
        boolean unknown = false;
        // A clause the check cannot read here owes nothing and proves nothing, and the two are not
        // the same answer. Kept apart: a clause that owes nothing because it folded to what it is read
        // with is discharged, and one that owes nothing because nothing here could be asked of it is
        // left to the run-time check.
        boolean unreadable = false;
        // A newtype construction from a value written out is the constant check's to report: it names
        // the clause that failed. It reads the construction as written, so a name given the value is
        // not one it sees, and this check says it instead — which is what `decidesFalse` carries.
        // The clauses that state something here, and not whether they are all of them: a clause
        // stating nothing readable at this construction is one the run-time check stands for, which
        // is what `unreadable` below already carries for the ones that were read.
        for (Clauses.Stated stated : clauses.statedAt(named, type, given).clauses()) {
            Predicates.Owed o = predicates.obligations(stated.expr(), k, at, unnamed, decidesFalse);
            unreadable |= o.unreadable();
            for (Predicates.Clause one : o.clauses()) {
                owed.add(new Owing(stated, one));
            }
        }
        if (owed.isEmpty()) {
            return new Judgment(unreadable ? Verdict.UNREPRESENTABLE : Verdict.PROVED, found);
        }
        NumericDomain<FactSubject> dom = readingOf(k.numbers(), owed);
        // The same clauses read against the same site, under what would be known here had no
        // condition on the path settled anything. What each clause states of the sizes it names holds
        // either way, so both readings take it.
        NumericDomain<FactSubject> alone = readingOf(k.unguarded().numbers(), owed);
        // An invariant is the conjunction of its clauses, so every one of them is read before what
        // the invariant came out as is decided. A clause the values alone refute is the whole
        // invariant refuted on the values alone, whatever another clause needed to be refuted —
        // stopping at the first refutation would answer with whichever clause was declared first.
        boolean alongside = false;
        for (Owing owing : owed) {
            Predicates.Clause c = owing.owed();
            ClauseStatus status = statusOf(c, dom, k, owing.clause());
            if (status == ClauseStatus.REFUTED) {
                if (c.refutedBy(alone, k.unguarded().facts())) {
                    refutedAlone = true;
                }
                alongside = true;
            } else if (status == ClauseStatus.UNKNOWN) {
                unknown = true;
            }
            put(found, owing.clause(), status);
        }
        if (refutedAlone) {
            return new Judgment(Verdict.REFUTED_ALONE, found);
        }
        if (alongside) {
            return new Judgment(Verdict.REFUTED_NOT_ALONE, found);
        }
        if (unknown) {
            return new Judgment(Verdict.UNKNOWN, found);
        }
        // Every clause that could be read is discharged. One that could not be read still stands, so
        // this is not the whole invariant proven.
        return new Judgment(unreadable ? Verdict.UNREPRESENTABLE : Verdict.PROVED, found);
    }

    /**
     * The domain {@code owed} is read against, built from what {@code base} holds.
     *
     * <p>Two steps that are one operation. What each clause states of the sizes it names is taken
     * as holding, and then what follows about the arithmetic the domain cannot carry — a product of
     * two values, a truncating quotient — is derived from what the reading proves of the values it
     * was computed from. The second reads the first: a size a clause bounds is one the arithmetic
     * over it can be read against, so the derivation has to come after, and a clause added to the
     * first step without the second being asked again is a construction judged against arithmetic
     * nothing was derived for. Written as one step so there is no order for a caller to keep.
     *
     * <p>Each reading answers with its own. A bound derived here is derived from what this reading
     * assumed, so it belongs to the reading and not to the value — which is why the construction's
     * two readings are built by two calls rather than sharing one domain.
     */
    private NumericDomain<FactSubject> readingOf(NumericDomain<FactSubject> base, List<Owing> owed) {
        NumericDomain<FactSubject> out = base;
        // What the clauses are decided by, which is one half of what the derivation can reach. The
        // other half is what the domain speaks of, and that is the domain's own to answer — asked
        // after this loop, since assuming a clause's statements is what puts its atoms there.
        Set<FactSubject> asked = new LinkedHashSet<>();
        for (Owing owing : owed) {
            Predicates.Clause c = owing.owed();
            for (Predicates.Constraint known : c.known()) {
                out = out.assume(known.form(), known.rel(), terms.kindsOf(known.form()));
            }
            asked.addAll(c.atomsItIsDecidedBy());
        }
        return DerivedBounds.refine(out, terms, asked);
    }

    /**
     * What was proved about one clause where the value is built.
     *
     * <p>Established and refused are asked for separately and are not each other's negation, so
     * asking one of them and reading the other off it is what puts a clause the check merely could
     * not decide among the ones a value fails. A clause that comes out both is neither: it says the
     * two questions were answered against a reading that proves everything, and a check that filed
     * it under either answer would report a clause the value does not fail, or leave one it does.
     */
    private static ClauseStatus statusOf(Predicates.Clause owed, NumericDomain<FactSubject> dom, Known k,
                                         Clause clause) {
        boolean established = owed.dischargedBy(dom, k.facts());
        boolean refused = owed.refutedBy(dom, k.facts());
        if (established && refused) {
            throw new Clause.NotOneClause("clause " + clause.id()
                    + " is established and refused by what is known where it is built");
        }
        if (established) {
            return ClauseStatus.SETTLED;
        }
        return refused ? ClauseStatus.REFUTED : ClauseStatus.UNKNOWN;
    }

    /** Records what was proved about {@code clause}, joining it with what is already there for it:
     * one clause reached twice — through two spreads, or read again under a rewrite — is one
     * clause. */
    private static void put(SequencedMap<Clause.Id, Judged> found, Clause clause,
                            ClauseStatus status) {
        found.merge(clause.id(), new Judged(clause, status), Judged::merge);
    }

    /**
     * One clause and what was proved about it.
     *
     * <p>The pair rather than a clause on one of two lists, so that a clause cannot be on two of
     * them: which of the three a clause came out as is one answer, and the set of clauses this check
     * read is partitioned by it rather than covered by sets that have to be kept apart.
     */
    record Judged(Clause clause, ClauseStatus status) {

        static Judged merge(Judged a, Judged b) {
            return new Judged(Clause.merge(a.clause(), b.clause()),
                    ClauseStatus.of(a.status(), b.status()));
        }

        /** The same, where the other reading did not read this clause. */
        Judged whereTheOtherReadingSaysNothing() {
            return new Judged(clause, status.whereTheOtherReadingSaysNothing());
        }
    }

    /** One obligation and the clause it was owed by. */
    private record Owing(Clauses.Stated from, Predicates.Clause owed) {

        /** The clause this was owed by: which one it is, what a sentence may call it, and where a
         * reader can be sent. None of those is read here — this hands the clause on whole, so that
         * a site choosing what to say asks it rather than being handed one of its answers. */
        Clause clause() {
            return from.clause();
        }
    }

    /**
     * What the check found: the verdict on the invariant, and the names of the clauses on each side
     * of it.
     *
     * <p>The verdict alone is what used to come back, and it is the conjunction's answer: a reader
     * told that a construction may violate "its invariant" is told nothing they can act on where the
     * type declares five clauses and four of them are settled.
     *
     * <p>{@code found} holds every clause that was read and what was proved about each, whether or
     * not the author named it and whether or not this compile can point at where it was written.
     * What a diagnostic can do with one of them is asked of the clause: that a warning could not
     * name a clause never meant there was no clause, and it does not now mean there is nowhere to
     * send a reader either.
     *
     * <p>One map and not a set per side, so a clause is on exactly one of them. The sides are read
     * off it: {@link #settled()} is what the guards establish, {@link #refuted()} is what the value
     * fails, and {@link #unsettled()} is the two the guards did not establish — which is the
     * question E2011 asks and E2010 does not.
     */
    record Judgment(Verdict verdict, SequencedMap<Clause.Id, Judged> found) {

        /**
         * What two readings of one construction found, together.
         *
         * <p>A clause is unsettled here if either reading left it so — what one branch established
         * is not established where the other did not — and refuted where either refuted it, a value
         * one branch rejects being a value rejected on a path that is reachable.
         *
         * <p>A clause only one of the readings read at all is a clause the other did not establish,
         * so it is kept where it stands and dropped where it was settled. What is kept for a clause
         * both readings found is the two joined rather than whichever arrived first: the readings
         * differ in what they could prove and not in what the declaration says, so the one fact that
         * may be in one and missing from the other is where the clause can be quoted from — and
         * taking the first would let the order the walk combines branches in decide whether a
         * warning points anywhere.
         */
        static Judgment of(Judgment a, Judgment b) {
            SequencedMap<Clause.Id, Judged> found = new LinkedHashMap<>();
            a.found().forEach((id, one) -> {
                Judged also = b.found().get(id);
                if (also != null) {
                    found.put(id, Judged.merge(one, also));
                } else if (one.status().unsettled()) {
                    found.put(id, one.whereTheOtherReadingSaysNothing());
                }
            });
            b.found().forEach((id, one) -> {
                if (!a.found().containsKey(id) && one.status().unsettled()) {
                    found.put(id, one.whereTheOtherReadingSaysNothing());
                }
            });
            return new Judgment(Verdict.of(a.verdict(), b.verdict()), found);
        }

        /** The clauses the guards did not establish — the ones this check could not settle and the
         * ones the value fails, which is what E2011 is about. */
        SequencedMap<Clause.Id, Clause> unsettled() {
            return where(ClauseStatus::unsettled);
        }

        /** The clauses the guards establish. */
        SequencedMap<Clause.Id, Clause> settled() {
            return where(status -> status == ClauseStatus.SETTLED);
        }

        /** The clauses the value being built fails wherever it is built, which is what E2010 is
         * about — and not every clause left standing beside them. */
        SequencedMap<Clause.Id, Clause> refuted() {
            return where(status -> status == ClauseStatus.REFUTED);
        }

        /**
         * The clauses a path read here fails, where no clause is failed on all of them.
         *
         * <p>What E2010 is about when the branches above a construction fail different clauses. The
         * invariant is refused whichever way the value comes, so the error stands; which clause it
         * is depends on the path, so none of them is one the value fails and the reader is sent to
         * each of them under what is true of it.
         */
        SequencedMap<Clause.Id, Clause> refutedSomewhere() {
            return where(status -> status == ClauseStatus.REFUTED_SOMEWHERE);
        }

        private SequencedMap<Clause.Id, Clause> where(Predicate<ClauseStatus> which) {
            SequencedMap<Clause.Id, Clause> side = new LinkedHashMap<>();
            found.forEach((id, one) -> {
                if (which.test(one.status())) {
                    side.put(id, one.clause());
                }
            });
            return side;
        }

        /** Whether a diagnostic can name a clause the guards did not establish. Not whether there
         * was one: a clause the author wrote no name on is in here and cannot be named. */
        boolean canNameUnsettled() {
            return canName(unsettled());
        }

        /** Whether a diagnostic can name a clause the guards did establish. Not whether there was
         * one, for the same reason. */
        boolean canNameSettled() {
            return canName(settled());
        }

        /** Whether a diagnostic can name a clause the value fails. */
        boolean canNameRefuted() {
            return canName(refuted());
        }

        private static boolean canName(SequencedMap<Clause.Id, Clause> side) {
            return side.values().stream().anyMatch(clause -> clause.name().isPresent());
        }

        /** Where the clauses on a side are, in the order they were declared — every one of them,
         * whether or not this compile has a file to quote it from. */
        static Stream<souther.compiler.diag.DiagnosticPlace> pointsTo(
                SequencedMap<Clause.Id, Clause> side) {
            return side.values().stream().map(Clause::at);
        }
    }

    /**
     * What a possible violation of {@code type}'s invariant is said as, which is two questions and
     * not one: whether a clause the guards did not establish can be named, and whether one they did
     * can be. Neither answers the other, and neither answers whether there was such a clause — a
     * clause written without a name is judged like any other and is in no set here.
     *
     * <p>Asked one at a time and of the sets, before anything is written out. One joined string
     * answering both is what ended this warning with `Established here: .`, and it could as easily
     * have dropped an established clause a reader could have been told about: the two mistakes are
     * the same mistake, and they are the two spellings this did not have.
     */
    private static Diagnostic.Builder mayViolate(Hir.Data type, Judgment judgment) {
        if (judgment.canNameUnsettled()) {
            if (judgment.canNameSettled()) {
                return Diagnostic.say(new InvariantMessage.TheGuardsDoNotEstablishButDoEstablish(
                        type.name(), names(judgment.unsettled()),
                        names(judgment.settled())));
            }
            return Diagnostic.say(new InvariantMessage.TheGuardsDoNotEstablish(
                    type.name(), names(judgment.unsettled())));
        }
        if (judgment.canNameSettled()) {
            return Diagnostic.say(
                    new InvariantMessage.TheGuardsDoNotEstablishTheInvariantButDoEstablish(
                            type.name(), names(judgment.settled())));
        }
        return Diagnostic.say(new InvariantMessage.TheGuardsDoNotEstablishTheInvariant(type.name()));
    }

    /**
     * The clause names as a diagnostic writes them out.
     *
     * <p>Reached only from a branch that has already chosen what to say. What decides which of the
     * spellings a diagnostic is written in is the set, and never this text: an empty string is what
     * a set with no names in it renders as, and reading it back as an answer puts "no clause was
     * named" and "there is no clause" into one value.
     */
    private static String names(SequencedMap<Clause.Id, Clause> clauses) {
        return clauses.values().stream().map(Clause::name).flatMap(Optional::stream)
                .map(ClauseName::value).collect(Collectors.joining(", "));
    }

    /** Whether the constant check reads this construction: a newtype's, over a value written where
     * it is built. That check names the clause that failed, so it is left to say it — and it reads
     * the construction as written, so a name given the value is not one it sees. */
    private static boolean constantlyBuilt(Hir.Data type, Core.Construct nd) {
        return type.newtype() && Terms.isWritten(nd.values().get(0).value());
    }

    /** Says what {@code verdict} found. A definite violation is an error and an unproven one a
     * warning; a discharged or non-expressible invariant says nothing. An {@code attempted}
     * construction raises no warning: what the warning reports is a possible abort, and an attempt
     * takes its else branch instead. */
    private void report(Core at, Hir.Data type, SourcePos pos, boolean attempted,
                        Judgment judgment) {
        Verdict verdict = judgment.verdict();
        List<Said> watching = WATCHING;
        if (watching != null && capturing == null) {
            watching.add(new Said(type.name(), pos, judgment));
        }
        if (capturing != null) {
            capturing.found().put(new Occurrence(asWritten(at)),
                    new Reported(type, pos, judgment, attempted));
            return;
        }
        switch (verdict) {
            case REFUTED_ALONE -> reportViolation(type, pos, judgment, false);
            case REFUTED_NOT_ALONE -> reportViolation(type, pos, judgment, true);
            case UNKNOWN -> {
                if (!attempted) {
                    warnings.add(finish(
                            mayViolate(type, judgment)
                                    .hint(new InvariantMessage.ReifyTheRelationOntoAnInput(
                                            type.name())),
                            pos, judgment.unsettled(),
                            new InvariantMessage.ThisClauseIsNotEstablishedHere()));
                }
            }
            // Nothing was asked here, so nothing is said. Whether that is the right thing to say of a
            // construction the check could not read is a question about what E2011 reports, and this
            // answers it the way it has always been answered.
            case UNREPRESENTABLE -> { }
            case PROVED -> { }
        }
    }

    /** What a construction came out as where it is being read on a branch rather than said. */
    private record Reported(Hir.Data type, SourcePos pos, Judgment judgment, boolean attempted) {

        Verdict verdict() {
            return judgment.verdict();
        }
    }

    /**
     * Which construction a reading found: the one in the body as it was written. A reading is that
     * body with a case split replaced, so the constructions along the way to the replacement are
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

    /** The node {@code e} was built from, however many rewrites ago. Asked of {@link Terms}, which
     * is where which-occurrence-is-this is answered: a construction and an evaluation are told apart
     * by the same rewrites, and two records of that would be two things to keep agreeing. */
    private Core asWritten(Core e) {
        return terms.asWritten(e);
    }

    /**
     * Where a walk is reading one arm, what it finds is collected here rather than said. A body
     * read on each arm of a case split reads every construction after it once per arm, and one
     * construction is one answer: it is the arms together that decide, the same as for a
     * construction the split is written inside.
     */
    private Capture capturing;

    /** What a reading has found so far. */
    private record Capture(Map<Occurrence, Reported> found) {

        static Capture empty() {
            return new Capture(new LinkedHashMap<>());
        }
    }

    /** What reading {@code e} finds. A branch nothing reaches finds nothing, which is the walk's
     * answer ({@link Known#reachesNothing}) and not a second one taken here: this collects what the
     * reading found and decides nothing about whether there was anything to find. */
    private Map<Occurrence, Reported> reading(Core e, Core unread, Known k, Denotations at,
                                              int cost) {
        Capture outer = capturing;
        Capture mine = Capture.empty();
        capturing = mine;
        try {
            entering(e, unread, k, at, cost);
        } finally {
            capturing = outer;
        }
        return mine.found();
    }

    /**
     * A case split a value is handed, and the bindings in scope where it stands. A case split is a
     * node answering one of several arms where which one is decided by something a reading can
     * assume — an {@code if} by its condition, a {@code match} by which case the scrutinee is — and
     * which arms those are is {@link #armsOf}'s answer, so nothing reading a site asks which of the
     * forms it was handed.
     *
     * <p>The node and the scope go together: a node is found by searching down from the outside, and
     * what it means is settled by where it was found, so a search that answered with the node alone
     * would leave the reading to work the scope out again — which is what it got wrong.
     *
     * <p>Every binder the search descends through is carried, and not only the ones a construction
     * outside could have been read against. What stands in scope decides two things: what the
     * condition settles about the value being built, and what the condition's own subtree means —
     * a construction written inside a condition is a construction like any other, and reading it
     * where its binders are not entered is reading it as something nothing can be said of.
     */
    private record SplitSite(Core split, List<Binder> scope, boolean read) {

        static SplitSite at(Core split) {
            return new SplitSite(split, List.of(), true);
        }

        /**
         * The same site, found past somewhere the reading stops.
         *
         * <p>What the reading covers is what {@link PathEngine#answering} walks from where the region
         * was entered, and the search below goes further: into a binding's body, into an arm, into an
         * attempt's success and into a departure. A site found there stands where nothing has been
         * read, so the branch put in its place is read here; a site the reading reached stands where
         * everything has, and reading it again would seed what is already held.
         */
        SplitSite pastTheReading() {
            return new SplitSite(split, scope, false);
        }

        /** One binder the split stands inside, as the environment its body is read in. */
        private interface Binder {
            Entered entering(PathEngine engine, Known k, Denotations at);
        }

        /** The same site, read from outside {@code binder} — so {@code binder} is the outermost of
         * what it is inside. */
        SplitSite under(Binder binder) {
            List<Binder> outer = new ArrayList<>();
            outer.add(binder);
            outer.addAll(scope);
            return new SplitSite(split, List.copyOf(outer), read);
        }

        /** A {@code let}'s body, read with the name standing for what it was given. */
        static Binder of(Core.LetIn li) {
            return (engine, k, at) -> engine.bindLet(li, k, at);
        }

        /** An attempted construction's success branch, read with the binding carrying the invariant
         * the attempt established. */
        static Binder of(Core.IfConstructed ic) {
            return (engine, k, at) -> engine.enteringBuilt(ic, k, at);
        }
    }

    /** One arm of a case split: what stands there, and what choosing it settles. */
    private record Arm(Core body, Choosing under) {}

    /** What choosing an arm settles, as somewhere to enter rather than as facts already derived.
     * Deferred because how many arms there are is what decides whether any of them is entered, and
     * entering one of a {@code match}'s is not free. */
    @FunctionalInterface
    private interface Choosing {

        Entered entering(Known within, Denotations there);
    }

    /**
     * A case split taken apart: what it asks to decide which arm it answers, and the arms it answers
     * one of.
     *
     * <p>One enumeration of the forms, so that nothing reading a split asks which of them it was
     * handed and no two readers can come to disagree about what a form's arms are. Its width is the
     * number of arms, which is what a reading of the body costs to open it.
     */
    private record Split(Core asked, List<Arm> arms) {}

    /** Whether a split of {@code width} arms is opened where the path has already cost {@code cost}
     * readings of the body.
     *
     * <p>Asked before the arms are entered, and about what opening it <em>would</em> cost: a bound
     * read after the fact bounds the path before the widest split on it and not the path.
     *
     * <p>The first split on a path is opened however wide it is. What it costs is its width and
     * nothing multiplies it, and refusing it would leave a {@code match} over a sum of more cases
     * than the bound read nowhere at all — which is the reading this bound is bounding rather than
     * something it is protecting against. So the bound is on the multiplying, and a path costs at
     * most the widest split on it or this bound, whichever is the larger. */
    private static boolean opens(int cost, int width) {
        return cost == 1 || (long) cost * width <= READINGS_A_PATH_MAY_COST;
    }

    /**
     * What {@code split} asks and what its arms are.
     *
     * <p>An {@code if} has two arms decided by its condition; a {@code match} has one per case,
     * decided by which case the scrutinee is — and an arm is entered <em>with</em> that scrutinee,
     * which is what says the value the arm binds is the one already there ({@link
     * PathEngine#enteringArm}) rather than a value of its own.
     *
     * <p>What a split asks is read where it stands, and read whatever it is: a construction written
     * in a condition or in a scrutinee is a construction like any other.
     */
    private Split splitOf(Core split) {
        return switch (split) {
            case Core.If iff -> new Split(iff.cond(), List.of(
                    new Arm(iff.then(), (within, there) -> new Entered(
                            predicates.assumeCond(iff.cond(), within, there, true).known(), there)),
                    new Arm(iff.els(), (within, there) -> new Entered(
                            predicates.assumeCond(iff.cond(), within, there, false).known(), there))));
            case Core.Match m -> new Split(m.scrutinee(), m.cases().stream()
                    .map(arm -> new Arm(arm.body(),
                            (within, there) -> engine.enteringArm(arm, m.scrutinee(), within, there)))
                    .toList());
            default -> throw new IllegalStateException(
                    "a site was opened at " + split.getClass().getSimpleName()
                            + ", which is not a case split — {@link #splitValueIn} and this answer for"
                            + " the same forms and one of them was given a form the other has not");
        };
    }

    /** Whether {@code e} is a case split — a node answering one of several arms, where which one is
     * decided by something a reading can assume. */
    private static boolean isASplit(Core e) {
        return e instanceof Core.If || e instanceof Core.Match;
    }

    /**
     * The first binding standing inside a value {@code e} is handed, or {@code null} where it is
     * handed none. What those values are is the same account as {@link #splitValueIn}'s: a
     * binding the walk steps into next is one it enters itself.
     */
    private static Core.LetIn bindingInValueIn(Core e) {
        return switch (e) {
            case Core.If iff -> bindingIn(iff.cond());
            case Core.IfConstructed ic -> bindingIn(ic.construct());
            case Core.LetIn li -> bindingIn(li.value());
            case Core.Match m -> bindingIn(m.scrutinee());
            default -> bindingIn(e);
        };
    }

    /**
     * The first binding standing inside {@code e}, or {@code null} where none stands there.
     *
     * <p>Where it looks is where the value is computed on the way to {@code e}'s own value, and it
     * stops at every place that is not: a branch, an arm, a departure and a closure's body are each
     * read with something entered that is not entered here — the condition that chose the branch,
     * what the arm binds, what the attempt built, what the closure was applied to. A binding lifted
     * out of one of those would be read where none of that holds, which is a construction read
     * against fewer facts than the source wrote it under. Each of them is where the walk goes next,
     * and what stands inside them is found again there, under what holds there.
     */
    private static Core.LetIn bindingIn(Core e) {
        return switch (e) {
            case Core.Block b -> null;
            case Core.LetIn li -> li;
            case Core.If iff -> bindingIn(iff.cond());
            case Core.IfConstructed ic -> bindingIn(ic.construct());
            case Core.Match m -> bindingIn(m.scrutinee());
            default -> {
                Core.LetIn[] found = new Core.LetIn[1];
                Core.forEachChild(e, child -> {
                    if (found[0] == null) {
                        found[0] = bindingIn(child);
                    }
                });
                yield found[0];
            }
        };
    }

    /**
     * The first case split {@code e} gives a value to, or {@code null} where it gives none. A split
     * in tail position — an {@code if}'s own branches, a {@code let}'s body, a case's body — is where
     * the walk goes next rather than a value it is handed, and a closure's body is read where the
     * closure is applied.
     */
    private static SplitSite splitValueIn(Core e) {
        return switch (e) {
            // Where the walk goes next is not a value it is handed: an `if`'s own branches, a `let`'s
            // body and a case's body are read after this, each with what is known there.
            case Core.If iff -> splitIn(iff.cond());
            case Core.IfConstructed ic -> splitIn(ic.construct());
            case Core.LetIn li -> splitIn(li.value());
            case Core.Match m -> splitIn(m.scrutinee());
            default -> splitIn(e);
        };
    }

    /** The first case split inside a value, with what it is inside. Everything under one is part of
     * it, including the body of a binding an expansion introduced — {@code let $0 = r in if $0.a > b
     * then ...} is a helper called on an argument, which is one value however many bindings writing
     * it took. Those bindings are what the split is read in the scope of; a binding is not in
     * scope for the value it is itself given, so a split found there is inside nothing. */
    private static SplitSite splitIn(Core e) {
        if (e instanceof Core.If iff) {
            return SplitSite.at(iff);
        }
        if (e instanceof Core.Block) {
            return null;   // read where the closure is applied
        }
        if (e instanceof Core.LetIn li) {
            SplitSite given = splitIn(li.value());
            if (given != null) {
                return given;
            }
            SplitSite inside = splitIn(li.body());
            return inside == null ? null
                    : inside.pastTheReading().under(SplitSite.of(li));
        }
        if (e instanceof Core.Match m) {
            // What it asks is computed on the way to its own value, so a split found there is inside
            // nothing and is the one to open. The `match` itself is the next one: it answers one of
            // its arms, and its arms are read as arms rather than searched for a split to lift out
            // of one — which is what leaves an arm's binding standing for the value it opened.
            SplitSite asked = splitIn(m.scrutinee());
            return asked != null ? asked : SplitSite.at(m);
        }
        if (e instanceof Core.IfConstructed ic) {
            SplitSite tried = splitIn(ic.construct());
            if (tried != null) {
                return tried;
            }
            SplitSite held = splitIn(ic.then());
            if (held != null) {
                return held.pastTheReading().under(SplitSite.of(ic));
            }
            // A departure stands where the invariant did not hold and nothing was built, so it is
            // inside nothing the attempt would have guaranteed.
            for (Core.ElseArm arm : ic.els()) {
                SplitSite departed = splitIn(arm.body());
                if (departed != null) {
                    return departed.pastTheReading();
                }
            }
            return null;
        }
        SplitSite[] found = {null};
        Core.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = splitIn(child);
            }
        });
        return found[0];
    }

    /**
     * {@code e} with every occurrence of {@code was} replaced by {@code becomes}. Occurrence is by
     * what it computes and not by where it is written: an author who writes one case split twice —
     * once to guard on and once to build from — wrote one value, and reading the two as two would
     * make the guard say nothing about what is built.
     */
    private Core without(Core e, Set<Core> was, Core becomes) {
        if (was.contains(e)) {
            return becomes;
        }
        if (e instanceof Core.Block) {
            return e;
        }
        Core made = Core.mapAll(e, child -> without(child, was, becomes), name -> name);
        if (made != e) {
            terms.rebuilt(made, e);
            // What an attempt tries to build is rebuilt through the construction slot, which does not
            // come back through here, so its rebuild is recorded here instead. Unrecorded, the two
            // readings key one construction under two occurrences, and the branch that refutes it is
            // said on its own rather than answered by the branch that proves it.
            if (made instanceof Core.IfConstructed x && e instanceof Core.IfConstructed from
                    && x.construct() != from.construct()) {
                terms.rebuilt(x.construct(), from.construct());
            }
        }
        return made;
    }

    /**
     * Every case split in {@code e} that computes what {@code value} computes, {@code value}
     * included. Asked once for all the readings, since which nodes those are does not depend on which
     * arm is being read.
     *
     * <p>{@code at} is where {@code value} stands, which is what keying it needs. A candidate
     * elsewhere in {@code e} is keyed there too rather than in its own scope, so two splits that
     * compute the same value under different bindings are read as two — which is the thing this
     * exists to prevent, still unanswered for that shape.
     */
    private Set<Core> sameSplit(Core e, Core value, Denotations at) {
        Set<Core> alike = Collections.newSetFromMap(new IdentityHashMap<>());
        alike.add(value);
        Term key = terms.bodyKey(value, at);
        if (key != null) {
            collectAlike(e, key, at, alike);
        }
        return alike;
    }

    private void collectAlike(Core e, Term key, Denotations at, Set<Core> alike) {
        if (e instanceof Core.Block) {
            return;
        }
        if (isASplit(e) && key.equals(terms.bodyKey(e, at))) {
            alike.add(e);
            return;
        }
        Core.forEachChild(e, child -> collectAlike(child, key, at, alike));
    }

    /**
     * Says of each construction the readings reached what all of them together decide. One that only
     * some readings reached is decided by those: the others did not discharge it because it was not
     * there to discharge.
     *
     * <p>As many readings as the split has arms, folded rather than taken two at a time. What that
     * rests on is {@link Judgment#of}, which is a join written so that the order branches are
     * combined in decides nothing — a clause both readings found is the two merged, and one only
     * one of them found is kept where it is unsettled. Folded over three arms or over two, the
     * answer is the same answer.
     */
    private void say(List<Map<Occurrence, Reported>> readings) {
        Set<Occurrence> at = new LinkedHashSet<>();
        readings.forEach(found -> at.addAll(found.keySet()));
        for (Occurrence one : at) {
            Reported said = null;
            Judgment judgment = null;
            for (Map<Occurrence, Reported> found : readings) {
                Reported reached = found.get(one);
                if (reached == null) {
                    continue;
                }
                said = said == null ? reached : said;
                judgment = judgment == null ? reached.judgment()
                        : Judgment.of(judgment, reached.judgment());
            }
            report(one.of(), said.type(), said.pos(), said.attempted(), judgment);
        }
    }

    /** Reports the violation, saying it in the terms {@code reason} was reached in: the value alone
     * fails the invariant on its own, or it fails under what else is known where it stands. The check
     * knows which of the two decided it and not what within the second did, so neither message names
     * a guard. */
    private void reportViolation(Hir.Data type, SourcePos pos, Judgment judgment,
                                 boolean onAPath) {
        Diagnostic.Builder said = rejects(type, judgment, onAPath);
        // The message says what holds of every path, so it names the clauses the value fails
        // wherever it is built. Where there are none it names none, and the regions then carry a
        // weaker claim about a wider set: the clauses some path here fails. Two sets, because they
        // are two claims — pointing at those clauses under the sentence's own words would say of
        // each that the value fails it, which the value coming down the other branch refutes.
        errors.add(CompileException.of(judgment.refuted().isEmpty()
                ? finish(said, pos, judgment.refutedSomewhere(),
                        new InvariantMessage.ThisClauseRejectsTheValueOnSomeOfThePathsHere())
                : finish(said, pos, judgment.refuted(),
                        new InvariantMessage.ThisClauseRejectsThisValue())));
    }

    /**
     * Where a report about a construction is, and where the clauses it is about are written.
     *
     * <p>Both places, in one place, because a report that gave itself a position and stopped there
     * still reads as a report — nothing about a warning that points only at the construction says a
     * clause was left unpointed at. Every one of these is built here, so a diagnostic added to this
     * check gets both or neither.
     *
     * <p>Which clauses is the caller's, and is not something this works out from a judgment: E2011
     * is about the clauses the guards did not establish and E2010 about the ones the value fails,
     * and those are the two questions the classification was split to keep apart. What this does
     * with the clauses it is handed is the same either way — every one of them that this compile can
     * quote, in the order the clauses were declared, labelled with what the caller says of them.
     *
     * <p>A clause this compile has no file for is said rather than left out: the label says where
     * the code came from and points at nothing ({@link souther.compiler.diag.DiagnosticPlace}). It
     * used to be dropped, so the same warning about the same rule told a reader which clause was at
     * issue when the declaration was in this project and told them nothing when it came off the
     * module path. What the message says is a different question with a different answer — whether
     * the clause could be named — and neither decides the other.
     */
    private static <M extends Message & Supporting> Diagnostic finish(
            Diagnostic.Builder said, SourcePos at, SequencedMap<Clause.Id, Clause> clauses,
            M label) {
        said.at(at);
        // One label per place, and the clauses are what there are several of. A label is a sentence
        // about a place, and where two clauses are written in one module this compile has no file
        // for, the place is all either of them has: what told the two labels apart was the caret,
        // and there is no caret. Said once each they come out as the same sentence twice, which
        // reads as a repeat rather than as two clauses. Which clauses they are is in the message,
        // which names them.
        java.util.Set<souther.compiler.diag.DiagnosticPlace> already = new java.util.LinkedHashSet<>();
        Judgment.pointsTo(clauses).forEach(place -> {
            if (!already.add(place)) {
                return;
            }
            switch (place) {
                case souther.compiler.diag.DiagnosticPlace.InSource in ->
                        said.secondary(in.region(), label);
                case souther.compiler.diag.DiagnosticPlace.Unavailable out ->
                        said.secondaryOutOfSight(out.provenance(), label);
            }
        });
        return said.build();
    }

    /**
     * What a refuted invariant is said as. One question here and not two, because what this error
     * reports is the clause the value fails and nothing else.
     *
     * <p>Which is why it is the refuted clauses that are named and not the unsettled ones. A value
     * that fails one clause may leave others standing that nothing here decides, and those are
     * clauses the guards did not establish rather than clauses the value fails — a sentence saying
     * "the value being built is one that clause rejects" over a list holding both says something
     * untrue of some of them.
     *
     * <p>A refuted invariant may well have clauses the guards established, and {@code judgment}
     * holds their names when it does — E2010 does not report them, which is a decision about what
     * this diagnostic is for and not an observation that there were none. Anything that starts
     * reporting them here asks {@link Judgment#canNameSettled()}, as the warning does, rather than
     * reading the answer off the set it is already writing out.
     */
    private static Diagnostic.Builder rejects(Hir.Data type, Judgment judgment, boolean onAPath) {
        if (onAPath) {
            return judgment.canNameRefuted()
                    ? Diagnostic.say(new InvariantMessage.TheValueIsRejectedOnAReachablePath(
                            type.name(), names(judgment.refuted())))
                    : Diagnostic.say(new InvariantMessage.TheValueIsRejectedOnAReachablePathUnnamed(
                            type.name()));
        }
        return judgment.canNameRefuted()
                ? Diagnostic.say(new InvariantMessage.TheValueIsOneTheInvariantRejects(
                        type.name(), names(judgment.refuted())))
                : Diagnostic.say(new InvariantMessage.TheValueIsOneTheInvariantRejectsUnnamed(
                        type.name()));
    }

    // --- introducing a binding -----------------------------------------------------------------

    /** Where {@code site}'s case split stands: {@code k} and {@code at} with every binder it is
     * inside entered, outermost first. */
    private Entered scopeOf(SplitSite site, Known k, Denotations at) {
        Entered in = new Entered(k, at);
        for (SplitSite.Binder binder : site.scope()) {
            in = binder.entering(engine, in.known(), in.at());
        }
        return in;
    }

    private Entered bindLet(Core.LetIn li, Known k, Denotations at) {
        return engine.bindLet(li, k, at);
    }

    private Entered enter(Core.Read root, Known known, Denotations at) {
        return engine.enter(root, known, at);
    }
}
