package souther.compiler.check;

import souther.compiler.types.BinOp;
import souther.compiler.values.AdmissibleValues;
import souther.compiler.ast.Hir;
import souther.compiler.check.Combinators.Handed;
import souther.compiler.check.PathEngine.Entered;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.InvariantMessage;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.Supporting;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.BlockReason;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
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
 * {@code Amount(-5)}); one it cannot prove is a warning (a possible abort — see below for what an
 * author answers it with). An invariant naming something it cannot name is left opaque (no
 * diagnostic; the run-time check stays), so every flagged construction is one whose clauses could be
 * read at the values it is being given.
 *
 * <p>What an author answers that warning with is one modelling question and not a list of moves:
 * whether the inputs the construction fails for are inputs the behavior takes. Where they are, the
 * failure is a business one and is written as a branch — by a guard, or by attempting the
 * construction, which is the same answer with the invariant written once instead of twice
 * (ADR-0070). Where they are not, the relation belongs to a data that owns it, and that data need
 * not already exist: a relation between two parameters belongs to no input, so writing it means
 * introducing the input that holds them both. Leaving the construction as written leaves the
 * warning unanswered — the run-time check still stands there, as it stands under every
 * construction, but standing is not an answer to what this check reported.
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

    /** One case split this walk decided about: how many times a reading of the body had already been
     * copied where the split stood, how many arms it has, and whether it was opened. */
    record Opening(int factor, int width, boolean opened) {}

    /**
     * Where a test in this package reads how far the splits down a path were opened, and null
     * everywhere else.
     *
     * <p>Beside {@link #WATCHING} and for the same reason, which this rule ran into rather than
     * being written for. How far splits are opened says nothing on its own: a split left unopened
     * leaves a value the reading has to bound some other way, and where another way answers — the
     * arms of a choice, taken together ({@link Derivation.Chosen}) — the construction over it is
     * discharged exactly as it is where the split was opened. So a test reading a warning was
     * reading the two together, and the day a second route bounded the same value it stopped
     * observing the bound at all.
     */
    static List<Opening> OPENING;

    /** One opened split: how many binders it stood inside, and whether what it handed its
     * continuation is the state that was read inside them. */
    record Carried(int binders, boolean handedOnWhatWasReadInside) {}

    /**
     * Where a test in this package reads what an opened split handed the expression it stands in,
     * one entry per split opened, and null everywhere else.
     *
     * <p>Beside {@link #OPENING} and for the reason that one gives. A split standing inside binders
     * is read inside them, and what it settles there is stated where the continuation is not — so
     * what may be handed on is that something leaves and not what was found. No diagnostic says
     * this: the facts that differ are about the binders themselves, which a continuation outside
     * cannot name, so nothing downstream reads them either way. What a reading of a warning would
     * be reading is whether some other route happened to establish the same thing.
     */
    static List<Carried> CARRIED;

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
     * How far the splits down one path are opened, which this walk holds itself to and does not own.
     *
     * <p>{@link ContextMultiplicity} owns it, because the walk over a region is not the only reader
     * that copies a reading by opening a split, and a limit belonging to one of them would say
     * nothing to the other. What this walk copies is a reading of the body; what the reading of a
     * derived value copies is an evaluation of the recipes. Different work, one way of multiplying
     * it, and it is the multiplying that is bounded.
     */
    private static final ContextMultiplicity ONE_READING = ContextMultiplicity.ofOneReading();


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
    /** Whether an evaluation can answer, which is what decides that a continuation is reached. */
    private final PathCompletion completion;
    private final List<CompileException> errors = new ArrayList<>();
    private final List<Diagnostic> warnings = new ArrayList<>();

    private InvariantChecker(Symbols symbols,
                             Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants,
                             ReadingPolicy policy) {
        this(symbols, dischargeInvariants, Map.of(), policy);
    }

    private InvariantChecker(Symbols symbols,
                             Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants,
                             Map<ValueName.Behavior, StatedContract> contracts,
                             ReadingPolicy policy) {
        this.engine = new PathEngine(symbols, dischargeInvariants, contracts, policy);
        // Named here because this check reads them directly and often. They are the engine's, not a
        // second copy: one engine builds them once and everything below sees those.
        this.symbols = engine.symbols();
        this.clauses = engine.clauses();
        this.terms = engine.terms();
        this.predicates = engine.predicates();
        this.completion = new PathCompletion(this.terms, this.predicates);
    }

    /**
     * How a clause of {@code data}'s invariant can be discharged, read on its own — the construction
     * is assumed to name what it is given, so what is left is the clause's own shape. {@code at} is
     * where the clause is written, which is the pre-expansion position; {@code clause} is that clause
     * in the representation the check reads.
     */
    public static ClauseDischarge capabilityOf(ClausesForDischarge.ClauseReading clause,
                                               TypeSymbol.AtModule named, Hir.Data data, Symbols symbols,
                                               ReadingPolicy policy) {
        InvariantChecker c = new InvariantChecker(symbols, Map.of(), policy);
        // Read over the declaration's own fields, each standing for itself: a construction hands one
        // value per field, so a clause naming a field names something wherever it is built. These
        // stand for a value rather than holding one, so they are entered as locations and nothing is
        // seeded of them — what a clause owes is the question, and answering it here would be
        // assuming it.
        return c.capabilityOf(clause, read -> c.clauses.typed(read, named, data),
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
     * <p>One answer, and the answer has a shape. What is written as one thing can be read as several
     * — a rule that names a helper is one thing to its author and is whatever that helper states to
     * this — so the answer may hold several {@link RequiredPart}s, every one of which has to be
     * established, and a part may admit several {@link StaticRoute}s, any one of which establishes
     * it. Flattened into one set of readings, a clause needing a bound in one part and a term in
     * another said that either guard discharges it, and the half an author did not pick is the one
     * they are about to be surprised by.
     *
     * <p>Where the answers are said is the clause's and is not passed in. A position that can be
     * passed can be passed from the wrong tree — which is what an expansion of the clause is, and
     * what every reader of this had to be told not to take it from. Handed the clause itself, there
     * is nothing left to get wrong: it says where it was written and what it comes to, and the two
     * were made together ({@link ClausesForDischarge}).
     *
     * @param clause the conjunct, as written and as this check reads it
     * @param typing what types the read form here — a declaration's fields, a signature's names —
     *               answering {@link TypedClause.Stopped} where typing it did not finish
     * @param locations the names it may read, each standing for itself
     * @param describing what is being read, for the record a fail-open leaves behind
     */
    static ClauseDischarge capabilityOf(StatedContract.Conjunct conjunct,
                                        Denotations locations, Symbols symbols,
                                        ReadingPolicy policy, String describing) {
        return new InvariantChecker(symbols, Map.of(), policy)
                .capabilityOf(conjunct.stated(), conjunct.at(), locations, describing);
    }

    /** What turns the read form of a clause into the tree this check walks, which is the reader's to
     * say: a declaration's clause is typed over its fields and a behavior's rule over its signature. */
    @FunctionalInterface
    interface Typing {
        TypedClause type(Hir.Expr read);
    }

    private ClauseDischarge capabilityOf(ClausesForDischarge.ClauseReading clause,
                                         Typing typing, Denotations locations, String describing) {
        return capabilityOf(typed(typing, clause.read(), describing), clause.at(), locations,
                describing);
    }

    /**
     * {@code read} as its reader types it, or that typing it did not finish.
     *
     * <p>Fail-open, as the walk is, and the two ways it can stop answer alike:
     * {@link TypedClause.Stopped} from this catch, and the same from the typing having caught
     * something of its own ({@link Clauses#typed}). Which is why the reading below reaches
     * {@link CapabilityResult.AnalysisStopped} from the answer and not only from here. A clause that
     * could not be typed is not a clause found to be outside the fragment: being inside it is what
     * was never asked.
     */
    private TypedClause typed(Typing typing, Hir.Expr read, String describing) {
        try {
            return typing.type(read);
        } catch (RuntimeException why) {
            gaveUp("typing " + describing, why);
            return new TypedClause.Stopped();
        }
    }

    /** The obligation {@code at} raises, and what came of reading {@code stated} for it. */
    private ClauseDischarge capabilityOf(TypedClause stated, SourcePos at, Denotations locations,
                                         String describing) {
        return new ClauseDischarge(new DischargeObligation(at),
                readingOf(stated, locations, describing));
    }

    /**
     * What the check made of {@code stated}: what the walk that reads clauses answered of it, or
     * that it never got to the end.
     *
     * <p>Nothing is worked out here. The fold, the parts and what the walk stopped on are that
     * walk's own answers, taken from the expression it normalizes and reads. Asked before it — of
     * the form an author wrote — {@code Int.compare(1, 2) >= 0} is a call and folds to nothing, and
     * the clause came back as a bound any guard implying it would discharge.
     */
    private CapabilityResult readingOf(TypedClause typed, Denotations locations, String describing) {
        if (!(typed instanceof TypedClause.Typed it)) {
            return new CapabilityResult.AnalysisStopped("typing " + describing);
        }
        try {
            return CapabilityResult.of(
                    predicates.assumed(it.value(), locations, false));
        } catch (RuntimeException why) {
            // Fail-open, as the walk is — and said as a stop rather than as a conclusion, because
            // what the clause is outside of is what this did not find out.
            gaveUp("capabilityOf " + describing, why);
            return new CapabilityResult.AnalysisStopped("capabilityOf " + describing);
        }
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
     *                 paths the stops happened at. A clause that could not be typed, and a walk that
     *                 stopped leaving rules nobody else reads ({@link PathEngine#leftBy}): in both,
     *                 a rule of the declaration is one no reading here ever saw, so no reading can
     *                 say it took that part of the declaration in. Not a walk that handed the rules
     *                 on — those are {@link #handedOn()}, and they are somebody's to read rather
     *                 than nobody's
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
     * @param handedOn the positions this reading ended at with a declaration still to be read under
     *                 them, which is an obligation on whoever walks the positions rather than
     *                 anything wrong here — see {@link Gathering#handedOn}
     */
    record Seeded(ConstraintState<FactSubject> constraints, Map<String, FactSubject> atoms, Map<String, FactSubject> keys,
                  Map<String, FieldDomains.Counted> held, Reading reading, ReadingEvidence took,
                  boolean everyClauseRead, Set<String> notGathered,
                  Set<String> unreadOfEveryValue, Set<String> handedOn,
                  Map<RuleRef, Map<Core, PartRead>> readBy,
                  Map<FactSubject, souther.compiler.numeric.Granularity> spacing) {

        /** The atom each count is recorded against, for a reader that wants the subject and not
         *  which operation it is a count of. Projected rather than kept beside {@link #held()}: two
         *  maps of one thing are what this pair was before (#1027). */
        Map<String, FactSubject> heldAtoms() {
            Map<String, FactSubject> out = new LinkedHashMap<>();
            held.forEach((path, counted) -> out.put(path, counted.atom()));
            return out;
        }

        public Seeded {
            notGathered = Set.copyOf(notGathered);
            unreadOfEveryValue = Set.copyOf(unreadOfEveryValue);
            handedOn = Set.copyOf(handedOn);
            // Insertion order, which is the order the declarations write their clauses. `Map.copyOf`
            // iterates in an order salted once per JVM run, and what is read off these is a list of
            // causes a report prints.
            readBy = java.util.Collections.unmodifiableMap(new LinkedHashMap<>(readBy));
        }

        /** What a walk that fell over comes to: no position named, no rule read, and saying so of
         *  every position, since nothing here knows which of them the rules were about. */
        static Seeded nothingRead() {
            return new Seeded(ConstraintState.<FactSubject>top(), Map.of(), Map.of(), Map.of(),
                    new Reading(List.of(), List.of(), Map.of(), Map.of(), Map.of(), Map.of()),
                    new ReadingEvidence(),
                    false, Set.of(FieldDomains.THE_VALUE), Set.of(FieldDomains.THE_VALUE),
                    Set.of(), Map.of(), Map.of());
        }

        /** The numbers alone, for the readers that are about intervals. Whether a value exists is
         * asked of {@link #constraints} and is never read off this. */
        NumericDomain<FactSubject> numbers() {
            return constraints.numbers();
        }
    }

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
     * <p><b>One of them is asked of a rule and the other of a position, and they are different
     * types for that reason.</b> Which rules are left out is a property of each rule — the
     * declaration that wrote it — and a rule a spread carries in was written where it was written,
     * whatever value it is being read at. Which names are not read at all is a property of the
     * position. The two are the same name only where a declaration writes its own clauses and
     * spreads nothing, and asked alike a spread rule was left in whatever a reader asked for, so
     * every end it held was held by nobody a report could name.
     *
     * @param withoutClauses which rules are left out, what is under the declarations that wrote
     *                       them still being read
     * @param stopAt         which declarations are not read at all
     */
    record Reach(RulesLeftOut withoutClauses, java.util.function.Predicate<TypeSymbol> stopAt) {

        /** Every rule, wherever it is written. */
        static final Reach EVERYTHING = new Reach(RulesLeftOut.NONE, _ -> false);

        /** Every rule but the ones {@code these} names wrote. */
        static Reach withoutClausesOf(java.util.function.Predicate<TypeSymbol> these) {
            return new Reach(RulesLeftOut.writtenOn(these), _ -> false);
        }

        /** Every rule that is not reached through one of {@code these}, they being supposed to hold
         * values whatever is written under them. */
        static Reach stoppingAt(java.util.function.Predicate<TypeSymbol> these) {
            return new Reach(RulesLeftOut.NONE, these);
        }
    }

    /** {@link Seeded} for one declaration. A declaration this cannot read is one whose fields it says
     * nothing about, which is the same answer as a declaration with no rules — so nothing about the
     * declaration throws. {@link Terms.OneTermTwoKinds} is not about the declaration and is not
     * caught ({@link #gaveUp}). */
    static Seeded seedFields(TypeSymbol.AtModule named, Hir.Data data, Symbols symbols,
                             ReadingPolicy policy) {
        return seedFields(named, data, symbols, policy, Map.of());
    }

    /**
     * {@link Seeded} with some of the fields already settled at a value.
     *
     * <p>What is left for the others, given those. The same domain and the same closure — settling a
     * field is one more assertion into it — so what comes back is the range each remaining field can
     * still take, which is where a row completing that assignment has to look.
     */
    static Seeded seedFields(TypeSymbol.AtModule named, Hir.Data data, Symbols symbols,
                             ReadingPolicy policy, Map<FieldDomains.Coordinate, Count> settled) {
        return seedFields(named, data, symbols, policy, settled, Reach.EVERYTHING);
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
    static Seeded seedFields(TypeSymbol.AtModule named, Hir.Data data, Symbols symbols,
                             ReadingPolicy policy, Map<FieldDomains.Coordinate, Count> settled,
                             Reach reach) {
        InvariantChecker c = new InvariantChecker(symbols, Map.of(), policy);
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
        // And of those, the ones a construction cannot get out of: what a position admits and
        // whether an edge of it may be promised are two questions, and a stop answers them apart.
        Set<String> unreadOfEveryValue = new LinkedHashSet<>();
        // The positions this reading ended at with the rules under them still to be read by
        // somebody. Kept apart from the stops above because it is an obligation and not a finding:
        // whether anything took the rules over is settled by whoever walks the positions, and the
        // answer is not in this reading at all.
        Set<String> handedOn = new LinkedHashSet<>();
        List<Written> written = new ArrayList<>();
        ReadingEvidence took = new ReadingEvidence();
        // What the bounds are able to state of each rule, as the reading that builds them says it.
        // Per part, because a rule is represented where every part of it is: a conjunct the bounds
        // hold nothing of leaves the range wider than the rule however well the conjunct beside it
        // went, and a set unioned over the whole clause says the opposite.
        Map<RuleRef, Map<Core, PartRead>> readBy = new LinkedHashMap<>();

        Gathering gathering = new Gathering() {

            @Override
            public void gathered(RuleRef.Invariant from, Core clause,
                                 Set<FactSubject> spokenFor) {
                written.add(new Written(from, clause));
                spokenFor.forEach(spoken -> took.record(from, spoken));
            }

            @Override
            public void missed(String path, Borne borne) {
                notGathered.add(path);
                if (borne == Borne.BY_EVERY_VALUE) {
                    unreadOfEveryValue.add(path);
                }
            }

            @Override
            public void handedOn(String path) {
                handedOn.add(path);
            }

            @Override
            public void constrained(RuleRef.Invariant rule, Core part, PartRead read) {
                readBy.computeIfAbsent(rule, _ -> new java.util.IdentityHashMap<>())
                        .put(part, read);
            }
        };
        try {
            // Not read at all, which is a question about this position and is asked once.
            boolean opened = !reach.stopAt().test(named);
            // And whether any rule of it was left out, which is asked of each rule. The two are
            // recorded at different grains on purpose: what is left out is a rule, and what is
            // missing from this reading is the position, since a clause of this declaration can
            // name any position of it.
            boolean skipped = false;
            if (!opened && !c.clauses.of(named, data).isEmpty()) {
                gathering.missed(FieldDomains.THE_VALUE, Borne.BY_EVERY_VALUE);
            }
            for (TypeOps.Declared declared :
                    opened ? c.clauses.declared(named, data) : List.<TypeOps.Declared>of()) {
                // Where this clause becomes a rule of the model something can be attributed to.
                // Everything below carries the origin as it is: what is written down here is read
                // back by a report, and a reader handed the clause reference instead would have to
                // decide for itself which of the rules that draw a line it was looking at. It is
                // also what says whether this reader asked for the rule at all.
                RuleRef.Invariant origin = new RuleRef.Invariant(Clause.Ref.of(declared));
                if (reach.withoutClauses().excludes(origin)) {
                    skipped = true;
                    continue;
                }
                Core stated = c.clauses.typed(declared.clause().expr(), named, data).orNull();
                if (stated == null) {
                    read = false;
                    gathering.missed(FieldDomains.THE_VALUE, Borne.BY_EVERY_VALUE);
                    continue;
                }
                written.add(new Written(origin, stated));
                Predicates.Owed owed = c.predicates.assumed(stated, at, false,
                        (part, said) -> gathering.constrained(origin, part, partRead(said)));
                // And the reading that builds the numeric constraints, said by what it produced.
                // `value * 2 >= 4` is beyond the two readings below and is taken in here about the
                // position itself; `value * value >= 4` comes back about an atom standing for the
                // product, which is not the position and is not a reading of it.
                Predicates.subjectsIn(owed).forEach(spoken -> took.record(origin, spoken));
                read &= !owed.unreadable();
                k = c.predicates.assume(owed, k, Known.Held.OF_THE_VALUE);
            }
            if (skipped) {
                // A rule of this value that no reading here took in, said once however many were
                // left out: what is recorded is which position is short, and the position is this
                // value either way.
                gathering.missed(FieldDomains.THE_VALUE, Borne.BY_EVERY_VALUE);
            }
            // And what each field's own type says of it, at the field's own location. A depth of one
            // is already spent on the record, so this reaches the field's newtype and stops where the
            // seeding of a parameter would.
            for (Map.Entry<String, BindingId> field : bindings.entrySet()) {
                Type type = fields.get(field.getKey());
                if (type != null) {
                    // Every position: this is the reading a boundary is derived from, and a rule
                    // the construction must satisfy is a rule wherever in the value it sits.
                    k = c.engine.seedAt(new Core.Read(field.getKey(), field.getValue(), type, NOWHERE),
                            data.newtype() ? FieldDomains.THE_VALUE : field.getKey(),
                            k, at, new GuaranteeWalk.Extent.EveryName(), gathering, reach);
                }
            }
            Map<String, FactSubject> atoms = new LinkedHashMap<>();
            Map<String, Type> typeAt = new LinkedHashMap<>();
            Map<String, FieldDomains.Counted> held = new LinkedHashMap<>();
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
            // Which values each position is left, off the clauses the walk reached. What reached this
            // value is the walk's answer and is given to both readings; what each of them makes of a
            // clause is its own, so neither can widen the other's idea of what it was handed.
            Map<FactSubject, Type> positions = positions(atoms, keys, typeAt);
            // How a choice holds what it leaves, settled over the whole declaration before any of
            // it is read. Its clauses are met, so what they come to together is the product of what
            // each comes to, and a bound on that bounds every step of the fold — which is why the
            // question is asked once here rather than of each clause as it arrives.
            long expansion = policy.expansionOf(written.stream().map(Written::clause).toList());
            Alternatives alternatives = policy.holdsApart(expansion)
                    ? Alternatives.APART : Alternatives.MERGED;
            // What puts two sets of values together, and what it is allowed to build doing it. One
            // for the whole of this value and not one per clause: what a position finally admits is
            // met from every rule that reached it, so a pattern in one clause and a pattern in
            // another pay into the same machine. Made per position inside — a complicated rule at
            // one position may not spend what a plain one at another was going to need, or which of
            // the two went unanswered would turn on the order they were written in.
            souther.compiler.values.Allowance<FactSubject> allowed =
                    souther.compiler.values.Allowance.ofAdmittedValues();
            Map<RuleRef, Map<Core, Set<FactSubject>>> adoptedBy = new LinkedHashMap<>();
            // One reader for this value's positions, used over however many clauses reach it, and
            // the one that decides the choices in what they came to.
            StatedByClauses.Reading reader = StatedByClauses
                    .readingOf(c.terms, at, positions, symbols, alternatives, allowed);
            // What each clause said and what each part of it said, kept as they were read and
            // asked afterwards. Which branch of a choice anybody can take turns on clauses not yet
            // read and on machines nobody has made at this point, and every one of these questions
            // has a different answer for a branch that survives and one that does not — a clause's
            // adoption included. Asked here, a reading answered from what it happened to hold, and
            // an account named a rule of a branch nothing satisfies.
            //
            // Kept in the order they were read and not in a map keyed by what a node happens to be,
            // because the order these are worked out in is the order the allowance is spent in: a
            // walk over an identity map would make what a declaration can be told exactly turn on
            // where its clauses landed in a table.
            StatedByClauses.Asked<Written> asked = new StatedByClauses.Asked<>();
            for (Written each : written) {
                asked.read(reader, each, each.clause());
            }
            // And now that every rule about this value has been said, what its positions admit is
            // worked out — and with it what each clause and each part of it took in, since a branch
            // decided is what every one of those turns on. Once, and here: a position's answer is
            // met out of every clause that reached it, so anything built before the last of them
            // arrived would be built out of less than the rules say — and which of two ways of
            // writing the same rules was affordable would be a fact about the writing.
            StatedByClauses.Answered<Written> answered = asked.resolve(reader, allowed);
            // What the answer has left, before a word of the account is read.
            Map<FactSubject, Integer> unspent = leftOf(allowed, positions.keySet());
            AdmissibleValues<FactSubject> values = answered.whole().values();
            answered.perClause().forEach((each, one) -> {
                one.adopted().forEach(position -> took.record(each.from(), position));
                took.stoppedBy(each.from(), one.aboutARule());
            });
            answered.perPart().forEach((each, parts) -> {
                Map<Core, Set<FactSubject>> out = adoptedBy
                        .computeIfAbsent(each.from(), _ -> new java.util.IdentityHashMap<>());
                parts.forEach(part -> out.put(part.getKey(), part.getValue().adopted()));
            });
            // And the same after it. Reading the account is reading an answer: the whole was worked
            // out once above, and what each clause and each part of it took in is looked up in
            // that. Worked out again per clause instead, asking what a rule adopted bought machines
            // the answer had no use for — so how exactly the rest of the declaration could be
            // answered depended on how much of its own account somebody had read.
            //
            // An assertion because it is about this compiler and not about any model, and here
            // rather than in one test because every declaration a corpus holds goes through it.
            // What comes after this line is the answer being carried on with, which may spend.
            assert unspent.equals(leftOf(allowed, positions.keySet()))
                    : "reading the account of " + named.name() + " spent its allowance";
            // What was counted bounds what was built, which is the whole of why counting before
            // reading is enough. It is an induction and its steps are held where they are taken —
            // a leaf is one alternative, a choice holds at most the sum and a conjunction at most
            // the product (`WhatACountTakenBeforeReadingPromisesAboutWhatIsBuilt`) — and it reaches
            // a clause at all because the count and the reading are one fold over it, so there is
            // no second walk to disagree about which shape is a choice.
            //
            // This is where the two ends are tied, over whatever declarations a corpus holds. An
            // assertion because it is about this compiler and not about the model, and because a
            // throw would be caught by the fail-open above and leave the reading silently dropped.
            assert alternatives == Alternatives.MERGED
                    || heldApart(values) <= expansion
                    : "a reading of " + named.name() + " expanded to " + heldApart(values)
                            + " alternatives past a counted " + expansion;
            // And which of the clauses place an edge, asked once the positions have names to be
            // recognised by.
            Reading reading = c.directsIn(written, at, atoms, keys, held, typeAt, took,
                    new PartsRead(readBy, adoptedBy));
            ConstraintState<FactSubject> constraints = k.constraints()
                    .takingValuesRead(values, allowed)
                    .taking(answered.whole().ordered());
            // How each atom's values are spaced, kept so that settling one afterwards states the
            // equality the same way this does. A count is a whole number of things whatever the
            // things are spaced by; a position's own value is spaced by its type.
            Map<FactSubject, souther.compiler.numeric.Granularity> spacing = new LinkedHashMap<>();
            atoms.forEach((path, atom) -> {
                Type type = typeAt.get(path);
                if (type != null) {
                    spacing.put(atom, c.terms.granularityOf(type));
                }
            });
            held.forEach((path, counted) ->
                    spacing.put(counted.atom(), souther.compiler.numeric.Granularity.DISCRETE));
            for (Map.Entry<FieldDomains.Coordinate, Count> each : settled.entrySet()) {
                FieldDomains.Coordinate where = each.getKey();
                // The number the caller settled, which is the position's own value or the count
                // taken of it. Two coordinates at one path and two atoms: a reading that resolved
                // only the first left a rule over two counts unconditioned while the same rule was
                // read whole when it was asked about.
                FactSubject atom = switch (where.kind()) {
                    case FieldDomains.CoordinateKind.OfItsOwnValue _ -> atoms.get(where.path());
                    // A count and nothing else. What a clause of a value has words for is the
                    // position and how much it holds; a number some other operation answers of the
                    // same location is a quantity the declarations never mention, so what they say
                    // about it is nothing rather than whatever stands in the count's slot (#1027).
                    case FieldDomains.CoordinateKind.OfWhatAnOperationAnswers taken ->
                            NumericMeasures.isMeasure(taken.operation())
                                    ? atomOf(held.get(where.path())) : null;
                };
                if (atom == null) {
                    continue;
                }
                // A count is a whole number of things, whatever the values counted are spaced by.
                souther.compiler.numeric.Granularity spaced = spacing.get(atom);
                if (spaced == null) {
                    continue;
                }
                constraints = ConstraintState.settling(constraints, atom, each.getValue(), spaced);
            }
            return new Seeded(constraints, atoms, keys, held, reading, took, read,
                    Set.copyOf(notGathered), unreadOfEveryValue, Set.copyOf(handedOn),
                    readBy, Map.copyOf(spacing));
        } catch (RuntimeException why) {
            gaveUp("seedFields " + named.name(), why);
            return Seeded.nothingRead();
        }
    }

    /** The atom of a count that may not be there, which every lookup of one wants. */
    private static FactSubject atomOf(FieldDomains.Counted counted) {
        return counted == null ? null : counted.atom();
    }

    /** The same over a whole reading, for the readers that take the map. */
    private static Map<String, FactSubject> heldAtomsOf(Map<String, FieldDomains.Counted> held) {
        Map<String, FactSubject> out = new LinkedHashMap<>();
        held.forEach((path, counted) -> out.put(path, counted.atom()));
        return out;
    }

    /** How many alternatives a reading came to, a reading that admits nothing holding none. */
    private static int heldApart(AdmissibleValues<FactSubject> values) {
        return values.held() instanceof AdmissibleValues.Held.Alternatives<FactSubject> it
                ? it.boxes().size() : 0;
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
                      Map<String, FieldDomains.Counted> held, Map<String, FactSubject> keys) {
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
        // The atom and the operation it counts by, which are one value. What the clauses of a value
        // have words for is the position and how much it holds, and the second of those is one
        // operation — the one that counts what the position's type holds. A coordinate that recorded
        // only "not the value" brought a count and a number some other operation answers of the same
        // location to one name (#1027).
        ValueName countsIt = NumericMeasures.takenOf(type, symbols);
        FactSubject counted = countsIt == null ? null : terms.takenAtomOf(value, type, at);
        if (counted != null) {
            held.put(path, new FieldDomains.Counted(counted, countsIt));
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
        if (depth > GuaranteeWalk.FIELDS_SEEDED) {
            return;
        }
        // What a clause of this value may name is the reading's answer and not a second
        // classification here: a record's fields, and the part a sum's cases share, which is
        // readable on a value of the sum exactly as a field of a record is. Which of these names a
        // row writes a value at is somewhere else's question — a name every case of a sum spreads
        // is written at the sum and stands under each of the cases.
        //
        // A name still worn here is one the walk above could not take off, which is a declaration
        // that returns to itself. Its `value` is this very value, so following it names the same
        // thing again a step deeper than anything asks about.
        Map<String, Type> under = switch (ValueReading.of(worn, symbols)) {
            case ValueReading.AtAValue read -> read.named();
            // Every name that comes off has come off above, so a name still worn is a declaration
            // that returns to itself: what it wraps is the value already being read, and reading it
            // again names that value at a path one `value` deeper than anything asks about.
            case ValueReading.UnderAName _ -> Map.of();
        };
        for (Map.Entry<String, Type> field : under.entrySet()) {
            name(new Core.FieldAccess(inner, field.getKey(), field.getValue(), NOWHERE),
                    GuaranteeWalk.under(path, field.getKey()), field.getValue(), at, symbols, depth + 1,
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
    record Direct(FieldDomains.Coordinate at, RuleRef.Invariant from,
                  InvariantBound bound, Core part, int conjunct) {

        /** Where in the value the end was placed. Never which end it is: one position carries more
         *  than one number and {@link #at} is what says which of them this is. */
        String path() {
            return at.path();
        }
    }

    /** One clause reaching a value, rebased onto the positions of that value, and which clause it
     * is. */
    private record Written(RuleRef.Invariant from, Core clause) {}

    /** What each of {@code positions} has left of its allowance, for holding an answer to what it
     *  spent between two moments. */
    private static Map<FactSubject, Integer> leftOf(
            souther.compiler.values.Allowance<FactSubject> allowed,
            Set<FactSubject> positions) {
        Map<FactSubject, Integer> out = new LinkedHashMap<>();
        positions.forEach(each -> out.put(each, allowed.left(each)));
        return out;
    }

    /**
     * Whether the value a stop left unread is one every value of what is being read has.
     *
     * <p>Two questions are asked of one stop and they do not have one answer. What a position admits
     * is short wherever a rule about it went unread; whether an edge may be promised is about what a
     * construction has to satisfy, and a rule about a value the construction need not make refuses
     * nothing at an edge of a field it must.
     *
     * <p>Which of the two a stop was is known where the stop is taken and nowhere after it, so it is
     * said there. Read off the path instead, a reader would be deciding from a spelling what the
     * walk knew.
     *
     * <p><b>Asked only of a stop, and never of a handing on.</b> Every way a walk stops short
     * leaves its rules unread and this says how much of the position they were about; whether some
     * rule below belongs to a reading opened elsewhere is a separate answer the reading gives beside
     * what it read ({@link Gathering#handedOn}). Nothing here decides that, and a position may
     * truthfully be both.
     */
    enum Borne {

        /** A construction has to make this value, so a rule under it can refuse the construction. */
        BY_EVERY_VALUE,

        /**
         * A value the construction need not make, so a rule under it refuses no construction.
         *
         * <p>The same reach {@link #everyRuleRead} has, and for the same reason: a rule four records
         * down the required chain refuses the outermost construction exactly as one on its own
         * fields does.
         *
         * <p>Which stops leave this is {@link PathEngine#leftBy}'s answer. What is worth knowing
         * here is that a required field of a type already entered comes back with this word and is
         * borne by every value: such a value cannot be built — a record that must hold its own kind
         * has no values — so no construction and no edge is decided by the answer. A model that
         * could be built there is one this would have to be told apart from.
         */
        BY_SOME_VALUES
    }

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
        void missed(String path, Borne borne);

        /**
         * A position where this reading ends and the rules under it become another reading's.
         *
         * <p>Not a rule missed. Nothing is declared at the position for this reading to take in,
         * and what is written under it is written about a value one position down, where a reading
         * of that declaration is opened and a row meets it. Which stops arrive here is
         * {@link PathEngine#leftBy}'s answer.
         *
         * <p>So this is an obligation and not a finding: something has to have taken the rules over,
         * and whoever walks the positions is the only one who can say whether anything did. Recorded
         * as a miss, the position above reported a rule nobody could ever discharge, because the
         * walk had gone to the rule at the position below (#1072). Read as nothing at all, a
         * position under which no reading was ever opened would claim to have read rules it never
         * saw.
         */
        void handedOn(String path);

        /**
         * What the reading that builds the bounds made of one part of {@code rule}, as it read it.
         *
         * <p>Per part, because a conjunction is one rule read a conjunct at a time and evidence
         * gathered for the whole answers a clause half of which nothing read on the strength of the
         * half that was. Recorded here so that nothing downstream reads the part a second time: two
         * readings of one conjunct agree only for as long as nobody changes one of them.
         */
        void constrained(RuleRef.Invariant rule, Core part, PartRead read);
    }

    /**
     * What each reading made of each part of each rule, as each of them said so while reading it.
     *
     * <p>Per part, because a conjunction is one rule read a conjunct at a time and evidence gathered
     * for the whole answers a clause half of which nothing read on the strength of the half that
     * was. Keyed by the part as the tree holds it, so the walk that reads the clause afterwards
     * finds this reading's own answer about the very node it holds rather than reading it again.
     *
     * @param read    what the reading that builds the numeric constraints made of each part
     * @param adopted what the reading that turns clauses into sets of values took each part in about
     */
    record PartsRead(Map<RuleRef, Map<Core, PartRead>> read,
                     Map<RuleRef, Map<Core, Set<FactSubject>>> adopted) {

        /** What the reading that builds the bounds made of {@code part} of {@code rule}, or null
         *  where it read no such part — which is not the same as having read it and made nothing of
         *  it. */
        PartRead readIn(RuleRef rule, Core part) {
            Map<Core, PartRead> said = read.get(rule);
            return said == null ? null : said.get(part);
        }

        Set<FactSubject> adoptedIn(RuleRef rule, Core part) {
            Map<Core, Set<FactSubject>> said = adopted.get(rule);
            return said == null ? null : said.get(part);
        }
    }

    /**
     * A part of a rule that the readings which seeded the value never read.
     *
     * <p>The seeding hands the whole clause to the readings this walk goes back over, so the two
     * meet the same parts. Where they do not, what one of them says about a conjunct is being asked
     * for a conjunct it never saw — and read as "nothing constrained here" it would answer for the
     * position that conjunct names.
     *
     * <p>Not an ordinary limit, so not swallowed. A shape a walk has no rule for leaves the run-time
     * check standing; this is the two walks disagreeing about what the clause is made of, and a
     * value that came back with nothing to say for that reason reads exactly like a value whose
     * rules were all read.
     */
    static final class APartNoReadingSaw extends TheCheckDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        APartNoReadingSaw(Core part) {
            super("a part of a rule the readings that seeded it never read: " + part);
        }
    }

    /** What one reading of one part came to, as the reading itself says it. */
    static PartRead partRead(Predicates.Owed said) {
        List<NumericConstraint> stated = new ArrayList<>();
        for (Predicates.Part eachC : said.parts()) {
            if (!(eachC instanceof Predicates.Part.Carried carriedC)) {
                continue;
            }
            Predicates.Clause c = carriedC.clause();
            if (c.numeric() != null) {
                stated.add(c.numeric());
            }
        }
        return new PartRead(Predicates.subjectsIn(said), Predicates.narrowableIn(said), stated);
    }

    /**
     * What the reading that builds the bounds made of one part of one rule.
     *
     * <p>What it was handed and not what the state looked like afterwards. A loss read off the
     * difference between two states is a loss the second occurrence of cannot be seen — the domain
     * holds which kinds of loss an atom has and not how many times each happened, so a second hole
     * dropped at an atom that already has one adds nothing to look for. And a loss is in any case a
     * fact about the step it happened at, while what a reader wants is whether the projection ends
     * up holding the rule. Both are answered by keeping what was given and asking the projection
     * this reading ended with, which is neither a second reading of the clause nor a summary of the
     * states in between.
     *
     * @param constrained the positions this part was read as speaking of, by any channel
     * @param narrowable  the atoms it was handed a form for
     * @param stated      the forms themselves, to be asked of the projection at the end
     */
    record PartRead(Set<FactSubject> constrained, Set<FactSubject> narrowable,
                    List<NumericConstraint> stated) {

        PartRead {
            constrained = Set.copyOf(constrained);
            narrowable = Set.copyOf(narrowable);
            stated = List.copyOf(stated);
        }
    }

    /**
     * A coordinate a clause reaching this value could be about.
     *
     * <p>The term itself, and not a path beside a flag saying a number was taken of it. A number
     * taken of a position is taken <em>by an operation</em>, and this reading knows which — a
     * {@code Counted} is recorded with it. Summarised as a boolean on the way out, two operations
     * over one path came back as one coordinate, and every reader downstream had a path and a flag
     * where the model had a term.
     *
     * @param carrier what its values are ordered on, or null where nothing here draws a line on
     *                them. Here rather than left out, because a coordinate is a coordinate whether
     *                or not an end can be read on it: gated on having one, a rule written about a
     *                position no line is drawn on named nothing, and the reading that could say so
     *                had never heard of the position
     */
    private record Coordinate(FieldDomains.Coordinate at, Carrier carrier) {

        /** Where in the value it sits. Never what it is: two numbers can be taken at one path, and
         *  {@link #at} is what tells them apart. */
        String path() {
            return at.path();
        }
    }

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
     *                  placing an end on it, outermost first. A declaration a module wrote, because
     *                  a clause is written on one: what reaches here is the {@code declaredOn} of
     *                  the clause's own reference, and a reader asking which module took an edge in
     *                  has the answer without a cast that could come back empty
     * @param raised    what each clause reaching this value raises, keyed on the rule it is.
     *                  Beside the ends rather than derived from them: a clause that placed no end
     *                  may have raised a question all the same, and a clause that placed one raised
     *                  more than the line. Nothing here says whether anything answered
     * @param raisedByPart the same, kept per part of each rule. A conjunction is one rule the author
     *                  wrote, and what it raises is what its conjuncts raise together — so a reader
     *                  that found one conjunct wanting and reached for the rule's questions would
     *                  name the positions of the conjunct written beside it as well
     */
    record Reading(List<Direct> directs, List<FieldDomains.NoLine> noLines,
                   Map<String, List<TypeSymbol.AtModule>> narrowers,
                   Map<RuleRef, Required> raised,
                   Map<RuleRef, Map<Core, Required>> raisedByPart,
                   Map<FieldDomains.BoundaryQuestion, FieldDomains.BoundaryStanding> standing) {}

    private Reading directsIn(List<Written> stated, Denotations at,
                                   Map<String, FactSubject> atoms, Map<String, FactSubject> keys,
                                   Map<String, FieldDomains.Counted> held,
                                   Map<String, Type> typeAt,
                                   ReadingEvidence took, PartsRead parts) {
        Map<FactSubject, Coordinate> byName = new LinkedHashMap<>();
        keys.forEach((path, key) -> {
            Carrier carrier = Carrier.ofValue(typeAt.get(path), symbols);
            byName.put(key, new Coordinate(FieldDomains.Coordinate.value(path), carrier));
            FactSubject atom = atoms.get(path);
            if (atom != null) {
                byName.put(atom, new Coordinate(FieldDomains.Coordinate.value(path), carrier));
            }
        });
        // A count is a whole number whatever it counts, so nothing about the container decides how
        // its sizes are spaced. The operation it is a count of comes from the reading that recorded
        // it: dropped here and rebuilt as "a number was taken", two operations over one path were
        // one coordinate and a report could not tell them apart.
        held.forEach((path, counted) -> byName.put(counted.atom(),
                new Coordinate(FieldDomains.Coordinate.takenBy(path, counted.by()),
                        Carrier.WHOLE)));
        List<Direct> out = new ArrayList<>();
        List<FieldDomains.NoLine> noLines = new ArrayList<>();
        Map<String, List<TypeSymbol.AtModule>> narrowers = new LinkedHashMap<>();
        Map<RuleRef, Required> raised = new LinkedHashMap<>();
        Map<RuleRef, Map<Core, Required>> raisedByPart = new LinkedHashMap<>();
        Map<FieldDomains.BoundaryQuestion, FieldDomains.BoundaryStanding> standing =
                new LinkedHashMap<>();
        stated.forEach(each ->
                direct(each.clause(), each.from(), new int[1], at, byName, out, noLines, narrowers, raised,
                        took, typeAt, parts, raisedByPart, standing));
        // Insertion order, kept: `Map.copyOf` iterates in an order salted once per JVM run, and
        // what a report prints for a position is these in the order the declaration writes them.
        return new Reading(List.copyOf(out), List.copyOf(noLines), Map.copyOf(narrowers),
                java.util.Collections.unmodifiableMap(new LinkedHashMap<>(raised)),
                java.util.Collections.unmodifiableMap(new LinkedHashMap<>(raisedByPart)),
                java.util.Collections.unmodifiableMap(new LinkedHashMap<>(standing)));
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
                        InvariantBound.Read placed,
                        Denotations at,
                        Map<FactSubject, Coordinate> byName, Map<RuleRef, Required> raised,
                        ReadingEvidence took, Map<String, Type> typeAt,
                        PartsRead parts,
                        Map<RuleRef, Map<Core, Required>> raisedByPart) {
        raises(raised, rule, states);
        // And what this part of it raises, kept apart from what the rule raises. A reader that found
        // one conjunct wanting reaches for this: the questions of the conjunct written beside it are
        // not what that conjunct left standing.
        raisedByPart.computeIfAbsent(rule, _ -> new java.util.IdentityHashMap<>())
                .merge(part, Required.ofInvariant(states), Required::and);
        // A part the reading of ends took in is accounted for by that reading, whatever shape the
        // clause has. Asked of the reading and not of the shape: the two were one question while a
        // bound this could fold was the only clause that arrived here as a bound, and reading the
        // shape for it would say that `value <= 10 * 2` went unadopted by a reading that never got
        // to look at it.
        //
        // A bound past where the order stops is not named here, and the walk below is what it gets.
        // It leaves nothing standing all the same — the numeric reading took the comparison in,
        // whatever the order had at the far end — and that is asserted rather than arranged for
        // (`AQuestionExistsBecauseTheModelStatesItAndNotBecauseAReadingSucceeded`), since a second
        // arm nothing observes is one that goes on being written after it stops being true.
        if (placed instanceof InvariantBound.Read.AnEnd) {
            return;
        }
        // The positions this part is about, by every name each answers to, since a reading files a
        // clause under whichever name it recognised.
        Set<String> named = states.about();
        Set<FactSubject> about = new LinkedHashSet<>();
        for (Map.Entry<FactSubject, Coordinate> each : byName.entrySet()) {
            if (named.contains(each.getValue().path())) {
                about.add(each.getKey());
            }
        }
        if (about.isEmpty()) {
            return;
        }
        Set<FactSubject> here = parts.adoptedIn(rule, part);
        // What this very reading made of this very part, as it said so when it read it. Asked
        // again here, the part was read a second time, and two readings of one conjunct agree only
        // for as long as nobody changes one of them.
        //
        // Absent rather than empty where the walk reaches a part the reading never read, which is
        // not a part that constrained nothing: read as one, a conjunct nobody saw would answer for
        // the position it names. The seeding hands the whole clause to the same reader this walks,
        // so there is no such part — and if the two ever come apart, this value reads as one whose
        // rules were not gathered rather than as one whose rules were read and said nothing.
        PartRead read = parts.readIn(rule, part);
        Set<FactSubject> constrained = read == null ? null : read.constrained();
        if (here == null || constrained == null) {
            throw new APartNoReadingSaw(part);
        }
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
    private void direct(Core clause, RuleRef.Invariant from, int[] conjunct, Denotations at,
                        Map<FactSubject, Coordinate> byName, List<Direct> out,
                        List<FieldDomains.NoLine> noLines,
                        Map<String, List<TypeSymbol.AtModule>> narrowers,
                        Map<RuleRef, Required> raised, ReadingEvidence took,
                        Map<String, Type> typeAt,
                        PartsRead parts,
                        Map<RuleRef, Map<Core, Required>> raisedByPart,
                        Map<FieldDomains.BoundaryQuestion,
                                FieldDomains.BoundaryStanding> standing) {
        if (clause instanceof Core.Binary and && and.op() == BinOp.AND) {
            // One rule the author wrote, so what it raises is what its conjuncts raise together.
            // Left before right, which is the order the clause was written in and the order
            // {@code ClauseHelpers.conjunctsOf} reads it in: the two readings of one clause number
            // its conjuncts alike, which is what lets a line drawn here be recognised as the line
            // the declaration's own reading drew (issue #1062).
            direct(and.left(), from, conjunct, at, byName, out, noLines, narrowers, raised, took,
                    typeAt, parts, raisedByPart, standing);
            direct(and.right(), from, conjunct, at, byName, out, noLines, narrowers, raised, took,
                    typeAt, parts, raisedByPart, standing);
            return;
        }
        // Which conjunct of the clause this is, taken here so that every one of them is numbered —
        // including the ones no end comes out of. Numbered only where a line was drawn, the count
        // would depend on what this reading could make of the conjuncts before it, and two readings
        // of one clause would disagree about which line is which.
        int part = conjunct[0]++;
        if (!(clause instanceof Core.Binary bin)) {
            settle(clause, from, states(clause, at, byName, null),
                    new InvariantBound.Read.NoEnd(),
                    at, byName, raised, took, typeAt, parts, raisedByPart);
            return;
        }
        if (!InvariantBound.ordering(bin.op()) && bin.op() != BinOp.EQ) {
            settle(bin, from, states(bin, at, byName, arithmeticOf(bin, at, byName)),
                    new InvariantBound.Read.NoEnd(),
                    at, byName, raised, took, typeAt, parts, raisedByPart);
            return;
        }
        // The coordinate-bearing side read as the left one, as `0 <= value` says what `value >= 0`
        // says.
        Coordinate found = byName.get(nameOf(bin.left(), at));
        Core bound = bin.right();
        BinOp op = bin.op();
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
        // What the clause is about, asked of the comparison and not of what `end` came to. A
        // coordinate compared for order against something naming no other coordinate states where
        // the values stop, whether or not the number on the other side is one this could fold.
        // Read once for this comparison and handed to both of the questions asked of it: what the
        // clause states, and what a reader is left with where no end came of it.
        Arithmetic read = arithmeticOf(bin, at, byName);
        ClauseStates shape = states(bin, at, byName, read);
        // And nothing of this value on the other side. `ARelation` is only what
        // `Relates.twoPositions` recognises, which wants each whole side to be a position — so
        // `width <= height + 1` is not one, and read as a bound it raised a question about where
        // `width` stops that no reading can ever answer, because a rule relating two positions
        // places no end (ADR-0090). The reader already knows: the reason it records for such a
        // comparison is `ComparisonBetweenPositions`.
        if (about != null && InvariantBound.ordering(op)
                && coordinatesIn(bound, at, byName).isEmpty()
                && shape instanceof ClauseStates.SomethingElse named) {
            Set<String> positions = new LinkedHashSet<>(named.positions());
            // The position the bound sits at, which the walk over the comparison names anyway. Added
            // so that the arm cannot be reached with nothing to be about.
            positions.add(about.path());
            // And the number the line is on, which is the coordinate this reading already holds. Not
            // rebuilt from the path: which of a position's numbers a line is on is what the operation
            // beside it says, and a reader handed the path alone has to go and ask something else.
            shape = new ClauseStates.ABound(about.at(), positions);
        }
        // And where this part raises the question of where the values there stop and no end came of
        // it, the answer to that question. Made once, when the question is first met: which limit
        // it is is read off the coordinate the question is keyed by, and the coordinate is what
        // carries the carrier — so the same reading of the same carrier is what any part raising
        // this question would come to, and it is done once rather than done again and reconciled.
        // What a part met afterwards adds is itself.
        if (shape instanceof ClauseStates.ABound stated
                && end instanceof InvariantBound.Read.NoEnd) {
            standing.compute(new FieldDomains.BoundaryQuestion(from, stated.line()),
                    (question, had) -> had == null
                            ? new FieldDomains.BoundaryStanding(
                                    UnreadComparison.whereALineWouldFall(about.carrier() != null),
                                    List.of(part))
                            : had.and(part));
        }
        settle(bin, from, shape, end, at, byName, raised, took, typeAt, parts, raisedByPart);
        if (end instanceof InvariantBound.Read.NoEnd) {
            // A rule saying where the values stop that no end came out of, said as that. Here,
            // where the reading gave up, because this is the reading a report's line would have
            // come from: the reading that turns clauses into sets of values has no word for a range
            // and calls every bound unread, and the accounting beside it answers whether anything
            // took the rule in — which a construction's discharge check does for a clause no line
            // was drawn from. Neither of them is the question, and both were being asked it.
            //
            // Per rule and not per position, as a `guard`'s comparison already is (spec
            // §example-partition). A position carries more than one statement, and an end read at
            // it says nothing about the rule beside it: kept as what the position was left with,
            // a bound on a field's own type swallowed the record's clause about the same field.
            noLineDrawn(bin, from, part, at, byName, noLines, read);
            // The declaration and not the clause. Which declaration took an edge in is what ADR-0090
            // names beside a line, and what a reader is sent to look at is the declaration holding
            // the relation.
            relating(clause, from.clause().id().declaredOn(), at, byName, narrowers);
            return;
        }
        if (end instanceof InvariantBound.Read.AnEnd placed) {
            out.add(new Direct(found.at(), from, placed.bound(), bin, part));
        }
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
     * What a comparison that placed no end is about.
     *
     * <p>Asked of the shape and not of what the reading managed. A rule relating two coordinates was
     * read to the end — both sides were recognised — and raises no question about one position; a
     * rule this made nothing of raises the same question every other rule about a position's values
     * raises, and is answered or not by whichever reading could take it in.
     */
    private ClauseStates states(Core clause, Denotations at,
                                Map<FactSubject, Coordinate> byName, Arithmetic read) {
        List<String> found = new ArrayList<>();
        namedIn(clause, at, byName, found);
        // What the rule cuts, ahead of what it looks like. Which values a rule restricts is settled
        // by the quantity its canonical form cuts, and that is the rule `UnreadComparison.why` is
        // written around one layer down — asked of what the rule cuts, and of the sides only where
        // that is unreadable. This reader was still asking the sides, so `lo - lo >= 0` came out as
        // a rule about `lo` and raised the questions a rule about a position raises: which values
        // may stand there, and where they stop. It states neither, so nothing could answer either.
        //
        // Only the empty quantity is read off here. A quantity over positions leaves which of them
        // the rule is about to the walk, which reads the same clause with the same coordinates, and
        // where the arithmetic read no quantity there is no fact to outrank a spelling with. The
        // order is what matters: a semantic answer, wherever this reader has one, comes first — so
        // the arithmetic growing able to read more moves this classification with it and nothing
        // below has to be touched.
        //
        // And only where the clause names a position at all. `1 >= 0` cuts nothing either, and it
        // is not a rule that restricts no value of this position — it is a rule about nowhere, said
        // by the one authority for that question, which is whether the value is mentioned.
        if (!found.isEmpty() && read != null && clause instanceof Core.Binary bin
                && read.holdsOfEveryRow(bin.op())) {
            return new ClauseStates.NoRestriction();
        }
        if (Relates.twoPositions(clause, e -> {
            FactSubject named = nameOf(e, at);
            return named != null && byName.containsKey(named) ? named : null;
        })) {
            return new ClauseStates.ARelation();
        }
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
                         List<String> out) {
        for (Coordinate each : coordinatesIn(e, at, byName)) {
            if (!out.contains(each.path())) {
                out.add(each.path());
            }
        }
    }

    /**
     * The coordinates {@code e} names, one per place, in the order the walk meets them.
     *
     * <p>Where a place answers to more than one name — a number is called one thing by the interval
     * algebra and another by everything else — the first is kept, which is the value's own
     * coordinate rather than a count taken of it. What is asked of one of these afterwards is what
     * its values are ordered on, and a count is ordered as a whole number whatever it counts.
     */
    private List<Coordinate> coordinatesIn(Core e, Denotations at,
                                           Map<FactSubject, Coordinate> byName) {
        Places places = placesIn(e, at, byName);
        List<Coordinate> out = new ArrayList<>();
        for (String path : places.origin().positions()) {
            out.add(places.met().get(path));
        }
        return out;
    }

    /**
     * What one expression is made of here, and which coordinate each place it named turned out to
     * be.
     *
     * <p>By the place and not by the whole of what a coordinate is. One place answers to more than
     * one name and the names carry the same rules, so a clause about one position is named once —
     * held under the coordinate instead, two names of one place would be two.
     */
    private record Places(ValueOrigin<String> origin, Map<String, Coordinate> met) {}

    /** What the place {@code path} is counted on, off whichever side of the comparison met it. */
    private static Carrier carrierAt(String path, Places left, Places right) {
        Coordinate here = left.met().containsKey(path) ? left.met().get(path)
                : right.met().get(path);
        return here == null ? null : here.carrier();
    }

    /**
     * What {@code e} is made of, in this reader's places.
     *
     * <p>The walk is {@link ValueOrigin}'s, so a clause and a {@code guard}'s comparison of the same
     * shape are taken apart the same way. What is this reader's own is the lookup: a clause names a
     * coordinate of the value it is written about, where a body names a position of an input.
     */
    private Places placesIn(Core e, Denotations at, Map<FactSubject, Coordinate> byName) {
        Map<String, Coordinate> met = new LinkedHashMap<>();
        ValueOrigin<String> origin = ValueOrigin.of(e, at,
                new ValueOrigin.Reading<String, Denotations>() {

            @Override
            public String positionOf(Core here, Denotations where) {
                FactSubject named = nameOf(here, where);
                Coordinate found = named == null ? null : byName.get(named);
                if (found == null) {
                    return null;
                }
                met.putIfAbsent(found.path(), found);
                return found.path();
            }

            /** A clause is written about the value in front of it, and there is no operation here
             *  that hands one of its parts out under a name of its own. */
            @Override
            public String madeFrom(Core here, Denotations where) {
                return null;
            }

            /**
             * What a name denotes, and the environment a {@code let}'s body is read in, both off
             * {@link Terms} — which is where a binding is entered for every reader that goes inside
             * one. Answered here instead, this would be a third account of what a name means beside
             * the two that already agree.
             */
            @Override
            public AffineForms.ReadThrough<Denotations> readThrough(Core.Read name,
                                                                    Denotations where) {
                return terms.readThrough(name, where);
            }

            @Override
            public Denotations inside(Core.LetIn li, Denotations where) {
                return terms.inside(li, where);
            }
        });
        return new Places(origin, met);
    }

    /**
     * What one ordering comparison that placed no end leaves for a report to say, at each position
     * it names.
     *
     * <p>Only an ordering. A rule of another shape — a format, a membership, an equality — says
     * which values exist and not where they stop, so naming it as a line nothing read would send an
     * author after a boundary nobody wrote; and an equality names a value rather than an end, which
     * a report has nowhere to put — saying it went unread would state an obligation that does not
     * exist yet.
     *
     * <p>One finding per position and not one per clause, because that is what a reader acts on and
     * what a {@code guard}'s comparison already produces: a clause relating two coordinates has no
     * single position to be filed under, and both sides of it are positions this drew no line
     * through.
     *
     * <p>Which limit stopped it is {@link UnreadComparison}'s, so a {@code guard} of this shape
     * cannot come to a different answer. What is read here is only what each side of the comparison
     * came to, which is this reader's own way of looking a coordinate up.
     *
     * <p><b>And which positions there are findings for is the quantity's where there is one.</b>
     * The walk says what each place the comparison mentions is called and which came first; the
     * quantity says which of them the rule is about. Taken from the walk, {@code x + y - y <= 20}
     * left a finding at {@code y} of a rule its own canonical form had cancelled — and the word
     * left there was the word for {@code x}.
     */
    private void noLineDrawn(Core.Binary comparison, RuleRef.Invariant from, int conjunct,
                            Denotations at,
                            Map<FactSubject, Coordinate> byName, List<FieldDomains.NoLine> out,
                            Arithmetic read) {
        if (!InvariantBound.ordering(comparison.op())) {
            return;
        }
        Places left = placesIn(comparison.left(), at, byName);
        Places right = placesIn(comparison.right(), at, byName);
        Predicate<String> ordered = place -> carrierAt(place, left, right) != null;
        Map<String, Coordinate> met = new LinkedHashMap<>();
        for (Coordinate each : coordinatesIn(comparison, at, byName)) {
            met.putIfAbsent(each.path(), each);
        }
        switch (read.quantity()) {
            case UnreadComparison.Quantity.Read<String> quantity -> {
                BlockReason.RuleWithoutLineReason why =
                        UnreadComparison.ofTheQuantity(quantity, ordered);
                for (String path : UnreadComparison.filedAt(quantity, List.copyOf(met.keySet()))) {
                    file(met.get(path), from, comparison, conjunct, why, out);
                }
            }
            // Where the reading stopped there is no quantity to be a subject, so every place the
            // walk met is asked, and asked for itself.
            case UnreadComparison.Quantity.NotRead<String> notRead -> {
                for (Coordinate each : met.values()) {
                    file(each, from, comparison, conjunct,
                            UnreadComparison.whereItStopped(ruleAt(each, left, right), notRead,
                                    ordered),
                            out);
                }
            }
        }
    }

    /**
     * What a rule filed at {@code where} is about, as this reader knows it.
     *
     * <p>What this reader supplies is what it calls the place. Whether the rule states anything
     * about the values standing there is the same question a body's comparison is held to, and is
     * answered where both readers meet it.
     */
    private static RuleAt<String> ruleAt(Coordinate where, Places left, Places right) {
        return UnreadComparison.subjectAt(where.path(), left.origin(), right.origin());
    }

    /** One finding, kept once. A coordinate reached twice is one place with one thing to say. */
    private static void file(Coordinate where, RuleRef.Invariant from, Core.Binary comparison,
                             int conjunct, BlockReason.RuleWithoutLineReason why,
                             List<FieldDomains.NoLine> out) {
        FieldDomains.NoLine said =
                new FieldDomains.NoLine(where.at(), from, comparison, conjunct, why);
        if (!out.contains(said)) {
            out.add(said);
        }
    }

    /**
     * What this reader's arithmetic made of one comparison, read once and projected twice.
     *
     * <p>Two questions come off one reading. Which coordinates the quantity is over is what says
     * whether a rule relates two positions or bounds one, and what is left when they cancel is what
     * says whether the rule holds of every row. Read separately, each reader called the same
     * arithmetic on the same two sides and the answers agreed only because the calls were the same
     * — which is the shape this branch removed from {@link ComparisonAssessment} at the other
     * producer, and put back here.
     *
     * @param quantity what the canonical form cuts, in the words {@link UnreadComparison} reads
     * @param residue  what is left of {@code left - right} once the positions have cancelled, or
     *                 null where the arithmetic stopped or a position is still in it
     */
    private record Arithmetic(UnreadComparison.Quantity<String> quantity,
                              java.math.BigDecimal residue) {

        /**
         * Whether the comparison holds of every row there is.
         *
         * <p>Two halves and both are needed. The positions have to cancel — the quantity is empty,
         * so no value of anything is either side of anything — and what is left has to be true.
         * {@code lo - lo >= 0} is {@code 0 >= 0}, which every row satisfies; {@code lo - lo >= 1}
         * is {@code 0 >= 1}, which no row satisfies, and a rule that admits nothing is the opposite
         * of one that restricts nothing. Read off the empty quantity alone, the two came out alike.
         *
         * <p>Every comparison and not the orderings alone. Which operator is written is no part of
         * whether a rule states anything: {@code lo - lo == 0} holds of every row exactly as the
         * first one does, and an author who wrote it would have been told that which values may
         * stand at {@code lo} is a question nothing answered. What the operator decides is what the
         * residue has to be, which is the switch here and nothing else.
         */
        boolean holdsOfEveryRow(BinOp op) {
            if (residue == null) {
                return false;
            }
            int sign = residue.signum();
            return switch (op) {
                case GE -> sign >= 0;
                case GT -> sign > 0;
                case LE -> sign <= 0;
                case LT -> sign < 0;
                case EQ -> sign == 0;
                case NE -> sign != 0;
                case AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
            };
        }
    }

    /**
     * That reading, made once for a comparison, or null where the operator is not one.
     *
     * <p>This reader's own, because the atoms are: a clause names a coordinate of the value it is
     * written about. What is done with the answer is {@link UnreadComparison}'s, so a {@code guard}
     * of the same shape in a body two declarations away is described in the same words — which is
     * what {@code invariant Int.add(length.value, width.value) <= 150} and the guard beside it are.
     */
    private Arithmetic arithmeticOf(Core.Binary comparison, Denotations at,
                                    Map<FactSubject, Coordinate> byName) {
        if (!comparison.op().compares()) {
            return null;
        }
        // Named against this reader's own coordinates rather than against every number the
        // discharge procedure can identify. A value that is a number and is no coordinate of the
        // subject is one the walk stops at, so the expression and its environment come back
        // together — read as an atom and found unprojectable afterwards, both were already gone.
        AffineForms.Outcome<FactSubject, Denotations> left =
                terms.outcomeOf(comparison.left(), at, byName::containsKey);
        AffineForms.Outcome<FactSubject, Denotations> right =
                terms.outcomeOf(comparison.right(), at, byName::containsKey);
        for (AffineForms.Outcome<FactSubject, Denotations> side : java.util.List.of(left, right)) {
            if (side instanceof AffineForms.Outcome.StoppedAt<FactSubject, Denotations> stopped) {
                return new Arithmetic(new UnreadComparison.Quantity.NotRead<>(
                        placesIn(stopped.node(), stopped.at(), byName).origin()), null);
            }
        }
        NumericDomain.LinearForm<FactSubject> whole =
                ((AffineForms.Outcome.Composed<FactSubject, Denotations>) left).form()
                        .minus(((AffineForms.Outcome.Composed<FactSubject, Denotations>) right)
                                .form());
        java.util.Set<String> over = new LinkedHashSet<>();
        for (FactSubject atom : whole.coefs().keySet()) {
            over.add(byName.get(atom).path());
        }
        if (over.isEmpty()) {
            return new Arithmetic(new UnreadComparison.Quantity.CutsNothing<>(), whole.constant());
        }
        if (over.size() == 1) {
            return new Arithmetic(new UnreadComparison.Quantity.OverOne<>(over.iterator().next()),
                    null);
        }
        return new Arithmetic(new UnreadComparison.Quantity.OverSeveral<>(over), null);
    }

    /**
     * Files {@code from} under every coordinate this comparison could carry a bound to.
     *
     * <p>Every coordinate it names and not only the two it compares: a bound reaches a position
     * along the differences, so a clause reading {@code a} is a way {@code a}'s edge can have been
     * moved even where the number came from somewhere further off.
     */
    private void relating(Core clause, TypeSymbol.AtModule from, Denotations at,
                          Map<FactSubject, Coordinate> byName,
                          Map<String, List<TypeSymbol.AtModule>> narrowers) {
        FactSubject named = nameOf(clause, at);
        Coordinate found = named == null ? null : byName.get(named);
        if (found != null) {
            List<TypeSymbol.AtModule> had =
                    narrowers.computeIfAbsent(found.path(), _ -> new ArrayList<>());
            if (!had.contains(from)) {
                had.add(from);
            }
            return;   // a coordinate names itself and nothing under it is a coordinate of its own
        }
        Core.forEachChild(clause, child -> relating(child, from, at, byName, narrowers));
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
                            Scope params, Symbols symbols, ReadingPolicy policy) {
        InvariantChecker c = new InvariantChecker(symbols, invariants, contracts, policy);
        if (body == null) {
            return new Findings(c.errors, c.warnings, Status.ABANDONED);
        }
        try {
            Entered in = new Entered(Known.top(), Denotations.none());
            for (Map.Entry<BindingId, Scope.Binding> p : params.bindings().entrySet()) {
                in = c.enter(new Core.Read(p.getValue().name(), p.getKey(), p.getValue().type(),
                        body.pos()), in.known(), in.at());
            }
            c.entering(body, in.known(), in.at(), ONE_READING);
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
     * Walks {@code e} as a region of its own, over what holds where the region begins.
     *
     * <p>Nothing more than that, and it used to be more. What the answers under {@code e} guarantee
     * was read here, over the whole subtree, before anything in it was walked — so a construction
     * standing in an argument was judged under what the call around it promises about the very
     * answer that argument has not yet produced, and under what a sibling evaluated after it
     * answers. Facts flowed backwards through the evaluation. They are taken in where the walk
     * evaluates the expression that answers them now ({@link PathEngine#answeredHere}), which is
     * the order they hold in.
     *
     * <p>What the region left, which is not the same as what holds outside it. An arm is read under
     * the condition that chose it and a binding's body under what the binding holds, and a caller
     * standing outside is somewhere none of that is true — so what a caller may take from this is
     * whether anything leaves at all, and the rest only where it can say that this region is the
     * whole of the way on ({@link #carriedOnFrom}).
     *
     * <p>Which is the whole of why this answers at all. It answered nothing while the walk did, and
     * kept on answering nothing after the walk began carrying what a step leaves into the next — so
     * every region boundary was a place the two halves came apart again: the facts were dropped,
     * rightly, and the one thing a caller is owed went with them. There is one rule and it is
     * applied at every boundary, rather than at the boundary a defect was found at.
     *
     * <p>Nothing reaches what this was handed, so there is nothing under it to be about. Asked here
     * and again in the walk, because the walk is itself where the conditions can come to contradict.
     */
    private Known entering(Core e, Known given, Denotations at, ContextMultiplicity copies) {
        if (given.reachesNothing()) {
            return given;
        }
        return walk(e, given, at, copies);
    }

    /**
     * What a fork leaves a continuation: what stood before it, what each way out of it left, and
     * where the ways were read.
     *
     * <p>A way that reaches nothing is not a way out. Where none is left, no run leaves the fork and
     * the continuation is reached by nothing — which is the fork's completion and is a different
     * thing from any of its arms' facts.
     *
     * <p>Where exactly one is left, what that way settled holds of the continuation. Not a branch
     * fact escaping its branch: a continuation reached through one way and through no other is
     * reached under what that way settled, and calling it a branch fact there would be reading the
     * fork as though it still had two.
     *
     * <p>And only where that way was read where the continuation stands. An arm reads its binding
     * under denotations the continuation is outside of, and what is stated there names a place a
     * caller cannot see; what survives such a way is that something did, and no more.
     *
     * <p>Which is what {@link Entered} is taken for and not a {@code Known} beside a
     * {@code Denotations}. Those are the two halves of one answer — a state and where it is stated —
     * and handed over as two parameters they can be got from two places: a state settled inside a
     * binder, paired with the denotations outside it, reads as a state that holds out there. Taken
     * as the pair, that is not a thing a caller can write.
     *
     * <p>Where more than one is left, what stood before the fork. Two states have no join here —
     * making one is a different thing to build — and what stood before them is what they still
     * agree on.
     */
    private static Known carriedOnFrom(Entered before, List<Entered> ways) {
        List<Entered> left = ways.stream().filter(w -> !w.known().reachesNothing()).toList();
        if (left.isEmpty()) {
            return before.known().reachingNothing();
        }
        return left.size() == 1 && left.getFirst().at() == before.at()
                ? left.getFirst().known() : before.known();
    }

    /**
     * One step of a region, over facts that already hold where the step begins — and what a
     * continuation of {@code e} inside this region may take out of it.
     *
     * <p><b>What is answered is what {@code e} having answered leaves true.</b> Everything
     * {@code e} evaluates on its way is walked first and in the order it runs
     * ({@link souther.compiler.core.Evaluated}), each handing what it left to the next, and what
     * {@code e} itself guarantees is added last ({@link PathEngine#answeredHere}) — because an
     * evaluation answers after the values it was computed from have answered. A construction is
     * therefore judged under what its own fields have answered and under nothing that is evaluated
     * after it.
     *
     * <p><b>Branch facts do not come out.</b> An arm is read under the condition that chose it and
     * a binding's body under what the binding holds, and neither is true of a continuation standing
     * outside; those are regions of their own ({@link #entering}) and answer nothing back. What
     * comes out of a fork is what the fork's own strict prefix left — its condition, its scrutinee,
     * the construction an attempt tried — and what the fork itself guarantees.
     *
     * <p>So a step that reaches nothing answers a state that reaches nothing, and every step after
     * it in the same region is handed one.
     */
    private Known walk(Core e, Known k, Denotations at, ContextMultiplicity copies) {
        if (k.reachesNothing()) {
            return k;
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
            Known held = standing.value() instanceof Core.Block ? k
                    : walk(standing.value(), k, at, copies);
            Entered in = bindLet(standing, held, at);
            // The rebuilt tree is the whole of this expression, so it is the one way on. What it
            // settles is inside the binder the expansion introduced and does not come back out;
            // that no run leaves it is about this expression and does.
            return carriedOnFrom(new Entered(held, at), List.of(new Entered(
                    entering(without(e, Set.of(standing), standing.body()), in.known(), in.at(),
                            copies),
                    in.at())));
        }
        SplitSite site = splitValueIn(e);
        Split split = site == null ? null : splitOf(site.split());
        // What the arms' readings are copied to, which is the same for every arm of the split: a
        // split is opened for all of them or for none, so nothing here spends against a sibling.
        ContextMultiplicity inAnArm = split == null ? null : opens(copies, split.arms().size());
        if (inAnArm != null) {
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
            // What the split asks is evaluated before any arm is, so it is walked here and what it
            // leaves is what the arms are read under.
            within = walk(split.asked(), within, there, copies);
            Set<Core> alike = sameSplit(e, value, there);
            // The readings start from where the split stood, not from outside it. The tree each is
            // given still holds those binders and walks into them again, which is why entering one
            // already entered is nothing: a second transition would forget what the arm settled.
            List<Map<Occurrence, Reported>> readings = new ArrayList<>();
            List<Entered> ways = new ArrayList<>();
            for (Arm arm : split.arms()) {
                Entered under = arm.under().entering(within, there);
                Read read = reading(without(e, alike, arm.body()), under.known(), under.at(),
                        inAnArm);
                readings.add(read.found());
                ways.add(new Entered(read.left(), under.at()));
            }
            say(readings);
            // The readings are the ways this expression is left, one per arm, and they are two
            // answers rather than one: what each found is said once ({@link #say}), and whether any
            // of them leaves anything at all is what a continuation after the split is reached by.
            // What the split asks was read inside every binder on the way down to it, so what it
            // settled is stated where the continuation is not. Taking it back out is the same rule
            // again — the binders are a region and the asking is its one way — and it is asked
            // before the arms are folded, so that what the arms are held against is a state the
            // caller can read.
            Known prefix = carriedOnFrom(new Entered(k, at), List.of(new Entered(within, there)));
            carried(site.scope().size(), prefix == within);
            return carriedOnFrom(new Entered(prefix, at), ways);
        }
        Known evaluated = switch (e) {
            case Core.Construct made -> {
                // The fields are what a construction evaluates, and it is built once they have all
                // answered — so it is judged after them and under what they left, and not before
                // them under what stood outside.
                Known out = evaluating(made, k, at, copies);
                if (out.reachesNothing()) {
                    yield out;
                }
                // A construction the value fails wherever it is built is one that aborts, so what
                // is written after it is written after nothing — the same shape as an operation
                // that answers no value, and taken in through the same door.
                yield carriedOn(out, refused(judge(made, out, at, false))
                        ? new Completion.CannotComplete(
                                new Completion.NoCompletionProof.RefutedConstruction(made))
                        : Completion.MAY);
            }
            case Core.If iff -> {
                Known out = walk(iff.cond(), k, at, copies);
                Known held = entering(iff.then(),
                        predicates.assumeCond(iff.cond(), out, at, true).known(), at, copies);
                Known otherwise = entering(iff.els(),
                        predicates.assumeCond(iff.cond(), out, at, false).known(), at, copies);
                yield carriedOnFrom(new Entered(out, at),
                        List.of(new Entered(held, at), new Entered(otherwise, at)));
            }
            case Core.IfConstructed ic -> {
                // The attempt's own construction cannot abort — a failing invariant is the else
                // branch — so it is checked for a decided violation and never warned about as a
                // possible one. Its field values are walked on their own so a construction nested
                // inside an argument is still an ordinary, aborting one.
                Known out = evaluating(ic.construct(), k, at, copies);
                if (out.reachesNothing()) {
                    yield out;
                }
                // An attempt is the one construction a failing invariant does not abort: the
                // departure is taken and the run carries on, so what this comes out as says nothing
                // about whether anything is reached.
                judge(ic.construct(), out, at, true);
                // Reaching `then` is the construction having held, so the binding carries the type's
                // invariant exactly as an input of that type does — which is a location, and not the
                // construction read again. What the construction denotes is what the check could say
                // of the attempt, and an attempt is written where it could not say enough: an
                // expression it cannot name denotes nothing, and inheriting that would drop the one
                // thing reaching this branch established.
                Entered in = engine.enteringBuilt(ic, out, at);
                List<Entered> ways = new ArrayList<>();
                ways.add(new Entered(entering(ic.then(), in.known(), in.at(), copies), in.at()));
                // Each departure stands where the invariant did not hold, and nothing was built
                // there, so none of them is seeded with anything the attempt would have guaranteed.
                Known departing = out;
                ic.els().forEach(arm ->
                        ways.add(new Entered(entering(arm.body(), departing, at, copies), at)));
                yield carriedOnFrom(new Entered(out, at), ways);
            }
            case Core.LetIn li -> {
                // A closure is read where it is applied: what its parameter holds is decided there,
                // and reading it here would read every construction in it with the element unknown.
                Known out = li.value() instanceof Core.Block ? k
                        : walk(li.value(), k, at, copies);
                Entered in = bindLet(li, out, at);
                // The body is the one way on: what a `let` answers is what its body answers, so a
                // body no run leaves is a `let` no run leaves.
                yield carriedOnFrom(new Entered(out, at), List.of(new Entered(
                        entering(li.body(), in.known(), in.at(), copies), in.at())));
            }
            case Core.Match m -> {
                Known out = walk(m.scrutinee(), k, at, copies);
                List<Entered> ways = new ArrayList<>();
                for (Core.Case c : m.cases()) {
                    // What the arm binds is a value of the case's type, reached only here, so it is
                    // a location this arm introduces and it carries what that type guarantees. What
                    // the scrutinee itself guarantees was read where the scrutinee stands, the part
                    // its cases share included, and is not read again under the case.
                    // The scrutinee travels with the arm: what a caller may assume of an answer is
                    // decided by which behavior answered and which case this arm opened, and the
                    // first of those is a question about what is being matched.
                    Entered in = engine.enteringArm(c, m.scrutinee(), out, at);
                    ways.add(new Entered(entering(c.body(), in.known(), in.at(), copies), in.at()));
                }
                yield carriedOnFrom(new Entered(out, at), ways);
            }
            case Core.PreservedCall call -> walkCall(call, k, at, copies);
            // A closure the reading stopped at, reached as a value like any other. What its body
            // answers is decided where the closure is applied, so nothing out here read it, and it
            // is a region of its own however it was arrived at.
            case Core.Block block -> {
                Core.forEachChild(block, b -> entering(b, k, at, copies));
                yield k;
            }
            default -> evaluating(e, k, at, copies);
        };
        if (evaluated.reachesNothing()) {
            return evaluated;
        }
        // Between the values this was computed from and what it answers, which is the one point the
        // question can be asked at: the operands have answered and this has not, so nothing here
        // assumes the very answer whose existence is being asked about. What comes back is about
        // the transition and is given to the continuation alone — this evaluation was walked, and a
        // construction standing among the values it was waiting on was judged on the way.
        Known carried = carriedOn(evaluated, completion.of(e, evaluated, at));
        return carried.reachesNothing() ? carried : engine.answeredHere(e, carried, at);
    }

    /**
     * {@code known} as a continuation of the evaluation {@code done} is about.
     *
     * <p>The one place a completion becomes a state, and the reason there is one: what shows that an
     * evaluation answers nothing differs — a primitive's arithmetic here, a construction the values
     * refuse there, and whatever comes to show it next — and what follows from it does not. The
     * proof is not read. What to tell an author about an evaluation no run leaves is a question
     * about diagnostics, and answering it here would tie a reporting policy to the mechanism.
     */
    private static Known carriedOn(Known known, Completion done) {
        return done instanceof Completion.CannotComplete ? known.reachingNothing() : known;
    }

    /**
     * What {@code e} evaluates, walked in the order it runs, each step handed what the one before it
     * left.
     *
     * <p>The order is {@link Evaluated}'s and not this walk's: a construction runs the field
     * declared first and not the one written first, and a second account of that here would be a
     * second thing to keep in step with the emitter. So is which steps run at all — a
     * short-circuiting operator's right operand runs on the runs its left did not answer for, and a
     * walk that decided that for itself would be a second reading of what {@code &&} means.
     *
     * <p>A step that runs only sometimes is a region, entered under what has to hold for it to run.
     * Which is the same treatment a branch gets and for the same reason: what it settles is true
     * only there, and an evaluation inside it that answers nothing stops nothing outside it.
     */
    private Known evaluating(Core e, Known k, Denotations at, ContextMultiplicity copies) {
        Known out = k;
        for (Evaluated.Step step : Evaluated.inOrder(e)) {
            switch (step) {
                case Evaluated.Step.Always(Core each) -> out = walk(each, out, at, copies);
                case Evaluated.Step.OnlyWhere(Core asked, boolean comesOut, Core each) -> {
                    // Two ways on, and the operator is the fork between them: the runs that
                    // evaluated this step, and the runs the left already answered for. A run leaves
                    // the operator down one of them, so what it leaves is what they leave.
                    Known taken = entering(each,
                            predicates.assumeCond(asked, out, at, comesOut).known(), at, copies);
                    Known skipped = predicates.assumeCond(asked, out, at, !comesOut).known();
                    out = carriedOnFrom(new Entered(out, at),
                            List.of(new Entered(taken, at), new Entered(skipped, at)));
                }
            }
        }
        return out;
    }

    /** Records what an opened split handed on, where a test in this package is reading them. */
    private static void carried(int binders, boolean handedOnWhatWasReadInside) {
        List<Carried> watching = CARRIED;
        if (watching != null) {
            watching.add(new Carried(binders, handedOnWhatWasReadInside));
        }
    }

    /**
     * Walks a call the representation kept standing, entering a combinator closure's parameters as
     * the locations the application introduces — the element at the container's element type, and
     * every other at what the closure was typed with — so a construction inside the closure is
     * analyzed rather than left opaque. A closure is where its parameters are values, which is here
     * and not where the block is written.
     *
     * <p><b>Every argument first, and the closure's body after all of them.</b> Evaluating a closure
     * position makes the function; the body runs inside the operation, which is entered once every
     * argument has answered. {@code List.map} takes the function before the container, so a body
     * read as the argument list was walked was read before the container was evaluated — under a
     * state missing what the container answered, and on runs the container's own evaluation stops
     * before the operation is ever entered. The first is the backward reading this walk was
     * straightened to end; the second is a construction judged after an abort, which is what all of
     * this is about. Both come of reading the body where the closure is written rather than where it
     * runs.
     */
    private Known walkCall(Core.PreservedCall call, Known k, Denotations at,
                           ContextMultiplicity copies) {
        Handed handed = Combinators.handedTo(call, at);
        // The arguments run in the order they are written, each over what the ones before it left.
        // A closure position evaluates nothing: it makes a function.
        Known out = k;
        for (Core arg : call.args()) {
            // The closure is asked by identity: a call may write one expression twice, and only the
            // argument the operation applies is the one an element arrives in.
            if (handed == null || arg != handed.closure()) {
                out = walk(arg, out, at, copies);
            }
        }
        if (handed == null || out.reachesNothing()) {
            // Nothing leaves the arguments, so the operation is never entered and the closure is
            // never applied.
            return out;
        }
        Core container = handed.container();
        Type elem = Terms.elementType(container.type());
        // The container is read under what every argument answered, which is what holds where the
        // operation is entered.
        List<Quantified> relations = predicates.elementRelations(container, out, at);
        Core.Read element = Terms.read(handed.element(), elem, handed.step().pos());
        // an element of a container is not a location the body can otherwise name
        Entered in = enter(element, out, at);   // the element carries its type's invariant
        // What a fold hands its step beside the element is a value of the type it was seeded
        // with, built through that type's checked constructor like any other — so it carries
        // that type's invariant, and the accumulator is not the one binding that has to give
        // its newtype up to be reasoned about.
        in = enterOthers(handed, in);
        Known k2 = in.known();
        for (Quantified q : relations) {
            k2 = predicates.instantiate(q, element, k2, in.at());
        }
        // A region of its own, and what it leaves stays in it: the body runs once per element, on
        // no element where the container is empty, and what it settles is not what the call answers.
        entering(handed.step().body(), k2, in.at(), copies);
        return out;
    }

    /** {@code in} with the closure's parameters other than the element entered at the types the
     * closure was typed with. A closure typed as anything but a function hands its parameters
     * nothing this can name, and they stay out. */
    private Entered enterOthers(Handed handed, Entered in) {
        if (!(handed.step().type() instanceof Type.FnOf fn)) {
            return in;
        }
        List<Core.Binder> params = handed.step().params();
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
    private Judgment judge(Core.Construct made, Known k, Denotations at, boolean attempted) {
        if (!(symbols.declarations().declaration(made.typeName()) instanceof Hir.Data type)) {
            return null;
        }
        Judgment judged = verdictOf(made, type, k, at);
        report(made, type, made.pos(), attempted, judged);
        return judged;
    }

    /** Whether the value a construction builds is one its invariant rejects wherever it is built,
     * which is the construction aborting. Which verdicts those are is {@link Verdict#refuted}'s to
     * say and is not counted again here — a second spelling of one set is a second set a verdict
     * added later can land in differently. */
    private static boolean refused(Judgment judged) {
        return judged != null && judged.verdict().refuted();
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
    private Judgment verdictOf(TypeSymbol.AtModule named, Hir.Data type, Map<BindingId, Core> given, Known k,
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
            for (Predicates.Part eachOne : o.parts()) {
            if (!(eachOne instanceof Predicates.Part.Carried carriedOne)) {
                continue;
            }
            Predicates.Clause one = carriedOne.clause();
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
     * <p>Two steps that are one operation, and both are inside {@link DerivedNumericFacts}: what
     * every value the reading can reach carries is taken as holding, and then what follows about the
     * arithmetic the domain cannot carry — a product of two values, a truncating quotient — is
     * derived from what the reading proves of the values it was computed from. The second reads the
     * first, so the order is not a caller's to keep and cannot be: a reading is made by the one
     * function that makes one ({@link DerivedNumericFacts#readingOf}).
     *
     * <p>Each reading answers with its own. A bound derived here is derived from what this reading
     * assumed, so it belongs to the reading and not to the value — which is why the construction's
     * two readings are built by two calls rather than sharing one domain.
     */
    private NumericDomain<FactSubject> readingOf(NumericDomain<FactSubject> base, List<Owing> owed) {
        // What the clauses are decided by, which is one half of what the reading can reach. The
        // other half is what the domain speaks of, and that is the domain's own to answer.
        Set<FactSubject> asked = new LinkedHashSet<>();
        for (Owing owing : owed) {
            asked.addAll(owing.owed().atomsItIsDecidedBy());
        }
        return DerivedNumericFacts.refine(base, terms, asked);
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
     * fails, and {@link #unsettled()} is the two nothing known there establishes — which is the
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

        /** The clauses nothing known there establishes — the ones this check could not settle and
         * the ones the value fails, which is what E2011 is about. */
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

        /** Whether a diagnostic can name a clause nothing known there establishes. Not whether there
         * was one: a clause the author wrote no name on is in here and cannot be named. */
        boolean canNameUnsettled() {
            return canName(unsettled());
        }

        /** Whether a diagnostic can name a clause that was established there. Not whether there
         * was one, for the same reason. */
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
     * not one: whether a clause nothing known there establishes can be named, and whether one
     * that was established can be. Neither answers the other, and neither answers whether there was
     * such a clause — a clause written without a name is judged like any other and is in no set
     * here.
     *
     * <p>Asked one at a time and of the sets, before anything is written out. One joined string
     * answering both is what ended this warning with `Established here: .`, and it could as easily
     * have dropped an established clause a reader could have been told about: the two mistakes are
     * the same mistake, and they are the two spellings this did not have.
     */
    private static Diagnostic.Builder mayViolate(Hir.Data type, Judgment judgment) {
        if (judgment.canNameUnsettled()) {
            if (judgment.canNameSettled()) {
                return Diagnostic.say(new InvariantMessage.NothingKnownHereEstablishesButDoesEstablish(
                        type.name(), names(judgment.unsettled()),
                        names(judgment.settled())));
            }
            return Diagnostic.say(new InvariantMessage.NothingKnownHereEstablishes(
                    type.name(), names(judgment.unsettled())));
        }
        if (judgment.canNameSettled()) {
            return Diagnostic.say(
                    new InvariantMessage.NothingKnownHereEstablishesTheInvariantButDoesEstablish(
                            type.name(), names(judgment.settled())));
        }
        return Diagnostic.say(new InvariantMessage.NothingKnownHereEstablishesTheInvariant(type.name()));
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
                                    .hint(new InvariantMessage
                                            .GuardItOrLetADataOwnTheRelation()),
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

    /**
     * One reading of an expression: what it found, and what it left.
     *
     * <p>Two answers and not one. What was found is said once over all the readings, since one
     * construction read on each arm is one construction ({@link #say}); what was left is per
     * reading, since it is that arm's run that either carries on or does not. Answered together
     * because they come of one walk, and a reader that had only the first would have to decide from
     * an empty list of findings whether the arm found nothing or was never entered — which are
     * different things and neither is the other's evidence.
     */
    private record Read(Map<Occurrence, Reported> found, Known left) {}

    /** What reading {@code e} finds, and what it leaves. A branch nothing reaches finds nothing,
     * which is the walk's answer ({@link Known#reachesNothing}) and not a second one taken here:
     * this collects what the reading found and decides nothing about whether there was anything to
     * find. */
    private Read reading(Core e, Known k, Denotations at, ContextMultiplicity copies) {
        Capture outer = capturing;
        Capture mine = Capture.empty();
        capturing = mine;
        Known left;
        try {
            left = entering(e, k, at, copies);
        } finally {
            capturing = outer;
        }
        return new Read(mine.found(), left);
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
    private record SplitSite(Core split, List<Binder> scope) {

        static SplitSite at(Core split) {
            return new SplitSite(split, List.of());
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
            return new SplitSite(split, List.copyOf(outer));
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

    /** What the readings of the arms of a split {@code width} arms wide are copied to, where the
     * body has already been copied {@code copies} times, or null where opening it would compound
     * past the limit.
     *
     * <p>{@link ContextMultiplicity#opening} decides it and this reports the decision, so what the
     * walk does and what a test in this package reads cannot come apart. */
    private static ContextMultiplicity opens(ContextMultiplicity copies, int width) {
        ContextMultiplicity opened = copies.opening(width);
        List<Opening> watching = OPENING;
        if (watching != null) {
            watching.add(new Opening(copies.factor(), width, opened != null));
        }
        return opened;
    }

    /**
     * What {@code split} asks and what its arms are.
     *
     * <p>Which values it answers one of, and what it asks to decide between them, are
     * {@link Choice}'s — this adds only what choosing each arm settles, which is the part needing an
     * environment. Read off the choice rather than off the node a second time: a reader taking the
     * arms out of the tree itself is a second answer to a question that has an owner, which is what
     * put an attempted construction outside every reading of it.
     *
     * <p>What a split asks is read where it stands, and read whatever it is: a construction written
     * in a condition or in a scrutinee is a construction like any other.
     */
    private Split splitOf(Core split) {
        Choice choice = Choice.of(split);
        if (choice == null) {
            throw new IllegalStateException("a site was opened at "
                    + split.getClass().getSimpleName() + ", which answers one value —"
                    + " isASplit and Choice.of were given a form one of them has not");
        }
        Core asked = null;
        List<Arm> arms = new ArrayList<>(choice.arms().size());
        for (Choice.Arm arm : choice.arms()) {
            Opened opened = opening(arm.decidedBy(), split);
            // The same node and not an equal one. Every arm of a split is decided by the one node
            // the choice was read off, so this is the node arriving as many times as there are arms;
            // a producer handing each arm its own has made something this reads by asking one thing
            // and there is no one thing to ask. Compared by identity because that is what is being
            // claimed, and because what stands in a scrutinee is a tree of any size.
            if (asked != null && asked != opened.asked()) {
                throw new IllegalStateException("the arms of a split at " + split.pos()
                        + " are decided by more than one node, and a split is read by asking one");
            }
            asked = opened.asked();
            arms.add(new Arm(arm.answers(), opened.choosing()));
        }
        return new Split(asked, arms);
    }

    /** What a split reads of one arm: the node deciding between the arms, and what choosing this one
     * settles.
     *
     * <p>Both out of one switch because both are this reader's projection of the same thing. What a
     * split asks is not a component of a choice — an operation defined by cases is decided by how its
     * arguments stand and by no node written down — so it is read here, from the way of deciding, by
     * the one reader that needs it. */
    private record Opened(Core asked, Choosing choosing) {}

    /**
     * What choosing the arm {@code decides} chose settles, as somewhere to enter.
     *
     * <p>The one reader here that has to grow when a kind of choice does, and the reason
     * {@link Choice.Decides} is a sum: a kind added without an arm here does not compile. Answering
     * by {@link Choice.Kind} instead let a kind be declared a split and reach no reader that opens
     * one — a decision recorded and then not carried out, which is a tripwire that reads as holding.
     *
     * <p>An attempt is not entered here. It is a choice this walk does not open as a split
     * ({@link #isASplit}) — it binds what it built, and the walk reads it where it stands with that
     * binding entered — so reaching this with one is the two disagreeing rather than a case to
     * handle.
     */
    private Opened opening(Choice.Decides decides, Core split) {
        return switch (decides) {
            case Choice.Decides.ACondition c -> new Opened(c.cond(), (within, there) -> new Entered(
                    predicates.assumeCond(c.cond(), within, there, c.holding()).known(), there));
            case Choice.Decides.ACase c -> new Opened(c.scrutinee(), (within, there) ->
                    engine.enteringArm(c.arm(), c.scrutinee(), within, there));
            case Choice.Decides.ItWasBuilt ignored -> throw notOpened(split,
                    "an attempted construction", "it is read where it stands with what it built"
                            + " bound");
            case Choice.Decides.ItDeparted ignored -> throw notOpened(split,
                    "an attempted construction", "it is read where it stands with what it built"
                            + " bound");
            case Choice.Decides.ByArgumentRelations ignored -> throw notOpened(split,
                    "an operation the library defines by cases", "there is no node to ask — what"
                            + " decides it is how its arguments stand, and the value is bounded by"
                            + " what its cases answer");
        };
    }

    /** Where the node being opened is, asked of the node and not of the way of deciding. A way of
     * deciding an arm need carry no node at all, and a message that read one off it had a position
     * for some of them and nothing for the rest. */
    private static IllegalStateException notOpened(Core split, String what, String instead) {
        return new IllegalStateException(what + " at " + split.pos()
                + " was opened as a case split, which this walk does not do — " + instead);
    }

    /**
     * Whether {@code e} is a case split this walk opens where it stands in a value position.
     *
     * <p>Not the same question as whether it is a choice, and answered from that one so the two
     * cannot drift. Every choice is a value that is one of several ({@link Choice}); a split is a
     * choice this walk reads by putting each arm where the choice stood and reading the body again.
     * An attempt is a choice and is not one of these: it binds what it built, and the walk reads it
     * where it stands with that binding entered ({@link PathEngine#enteringBuilt}) rather than by
     * substituting its arms. An operation the library defines by cases is not one either, and for a
     * plainer reason: a split is read by asking the node that decides it, and how two arguments stand
     * is not a node anybody wrote. Where it stands inside a value the walk does not read it that way and
     * the value is bounded by its arms instead ({@link Derivation.Chosen}).
     *
     * <p>Written as a switch over {@link Choice.Kind} with no default, so a kind of choice added
     * later is one this stops at until someone says which of the two it is. That is not by itself
     * enough and was once all there was: a kind can be answered {@code true} here and still reach no
     * reader that opens one. What carries the decision out is that this is the one gate — {@link
     * #splitIn} finds a site by asking it, and {@link #splitOf} reads the arms off the same
     * {@link Choice} — and that {@link #choosing} switches over {@link Choice.Decides}, which is
     * sealed, so a kind declared a split with nothing to enter it by does not compile.
     */
    private static boolean isASplit(Core e) {
        Choice choice = Choice.of(e);
        return choice != null && switch (choice.kind()) {
            case A_CONDITION, A_CASE -> true;
            case AN_ATTEMPT, THE_ARGUMENTS -> false;
        };
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
                    : inside.under(SplitSite.of(li));
        }
        if (e instanceof Core.Match m) {
            // What it asks is computed on the way to its own value, so a split found there is inside
            // nothing and is the one to open. The `match` itself is the next one: it answers one of
            // its arms, and its arms are read as arms rather than searched for a split to lift out
            // of one — which is what leaves an arm's binding standing for the value it opened.
            SplitSite asked = splitIn(m.scrutinee());
            if (asked != null) {
                return asked;
            }
        }
        if (e instanceof Core.IfConstructed ic) {
            SplitSite tried = splitIn(ic.construct());
            if (tried != null) {
                return tried;
            }
            SplitSite held = splitIn(ic.then());
            if (held != null) {
                return held.under(SplitSite.of(ic));
            }
            // A departure stands where the invariant did not hold and nothing was built, so it is
            // inside nothing the attempt would have guaranteed.
            for (Core.ElseArm arm : ic.els()) {
                SplitSite departed = splitIn(arm.body());
                if (departed != null) {
                    return departed;
                }
            }
            return null;
        }
        // Asked after the descents above and not instead of them: where a split stands inside what
        // this node computes on the way to its own value, that one is the one to open. Which nodes
        // reach here at all is the one question about it ({@link #isASplit}), so a kind of choice is
        // opened by this walk or is not, and never by one reader and not another.
        if (isASplit(e)) {
            return SplitSite.at(e);
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
     * is about the clauses nothing known there establishes and E2010 about the ones the value fails,
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
     * clauses nothing known there establishes rather than clauses the value fails — a sentence saying
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
