package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.flow.Arrival;
import souther.compiler.flow.Paths;
import souther.compiler.flow.ValueArrivals;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.observe.Figure;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The rules of the decision one body states.
 *
 * <p>The ways through the body, each carrying the conditions it consulted. Read straight off the
 * evaluation and never assembled from a table of every assignment: what makes a condition absent
 * from a rule is the path having settled before reaching it, so the short-circuit is the rule and
 * there is nothing left to fold afterwards.
 *
 * <p><b>The ways are {@link ValueArrivals}'s and the words for them are this reading's.</b> Which
 * ways a body has is what the body does, and it is answered with no naming at all; a second walk of
 * the body to enumerate them would be a second account of what the body does, free to disagree with
 * the first the day either learns to read a shape. What is this reading's own is
 * {@link DecisionNaming} — which distinctions a way turns on, and what tells one from another.
 *
 * <p>Of the body the analysis reads, which is the tree the language's own operations stand in. A
 * rule an author wrote through one of them is a rule of the model, and the tree that runs has it
 * expanded into what it does — where the ways through the expansion are the operation's and not the
 * author's.
 *
 * <p><b>A path assuming a proposition both ways is not a rule.</b> Two readings of one column that
 * disagree are refused where the ways are joined, so a contradiction never becomes a rule and
 * nothing is dropped for want of a witness.
 *
 * <p>Nothing here says a rule can be reached. A vector says what a row would have to satisfy;
 * whether anything stands there is settled against the rows and a stated search, and is no part of
 * reading the body.
 *
 * <p><b>But a way no input takes is not read on.</b> Where the conditions a way has come to are
 * proved to leave no input at once ({@link DecisionNaming#join}), every rule past it is one no run
 * takes, and there are as many of those as there are ways to go on. The way is held once, with the
 * proof, and stands for all of them: written out, a chain of helpers each settling the next would
 * be a rule for every way the chain cannot go.
 *
 * @param behavior    whose decision this is
 * @param found       the rules, in the order the reading holds the ways, each with what a run down
 *                    its path would be seen doing
 * @param excluded    the ways no rule past which is owed a row — no input takes it, every run of
 *                    it stops at a construction, or a proof stopped at a figure did not tell
 *                    which ({@link Excluded}) — each where the proof was had
 *                    and none narrower than another, in the order the reading met them; the rules
 *                    past each are in none of {@code found}
 * @param enumeration whether every way was written down
 * @param metAt       where this reading met each condition it places itself, which is what a
 *                    report about one of them is sent to
 *                    ({@link ConditionReportAnchor.WhereTheReadingMetIt}). This reading's own: a
 *                    condition is named by the reading that met it, and the same name from
 *                    another reading is another condition
 */
public record DecisionReading(String behavior, List<Ruled> found, List<Excluded> excluded,
                              Enumeration enumeration, Map<ConditionOccurrence, Citation> metAt) {

    /** The figure this reading stops at, read here rather than written here. */
    private static final CompositionBudget PATHS_READ = CompositionBudget.PATHS_OF_A_DECISION_READ;

    public DecisionReading {
        found = List.copyOf(found);
        excluded = List.copyOf(excluded);
        // In the order the reading met them, which is an order nobody reads and the one a copy
        // that kept none would replace with the run's.
        metAt = Collections.unmodifiableMap(new LinkedHashMap<>(metAt));
    }

    /**
     * One rule, and where a run that took its path would be recorded.
     *
     * <p>The two apart because a rule is told apart by the distinctions it consulted and not by
     * where they are written. Held inside the rule, one body stating one rule in two places would
     * state two.
     *
     * @param steps every condition the path consulted, in the order it met them, each with what it
     *              states and asks. What the way is said as, states and asks is read off these
     * @param whole whether every condition on the way was one this reading has words for. A path
     *              that is not is a rule this compiler read less of than the body states, which is
     *              a weakening of the measurement rather than a rule the body does not have
     */
    public record Ruled(DecisionRule rule, List<RuleStep> steps, boolean whole,
                        List<PassedConstruction> passed) {

        public Ruled {
            steps = List.copyOf(steps);
            passed = List.copyOf(passed);
        }

        /** The same, of a path that goes through no construction. */
        public Ruled(DecisionRule rule, List<RuleStep> steps, boolean whole) {
            this(rule, steps, whole, List.of());
        }

        /** Every condition the path consulted, said as what a run through it would be seen
         *  doing. */
        public List<ShownBy> shownBy() {
            return steps.stream().map(RuleStep::shown).toList();
        }

        /** The same conditions in the words a composer of a row works from, with what getting past
         *  each construction on the way states: what a row standing in this rule would have to
         *  satisfy of the input. */
        public WayToTheBorder states() {
            List<OnTheWay> stated = new ArrayList<>();
            steps.forEach(each -> stated.addAll(each.states()));
            passed.forEach(each -> stated.addAll(each.states()));
            return WayToTheBorder.forArrival(stated);
        }

        /** What a row has to be, beside the way, for each case the statements on this path draw
         *  inside themselves that the reading can say it of. */
        public List<CaseWay> caseWays() {
            return steps.stream().flatMap(each -> each.cases().stream()).toList();
        }

        /** The way to this rule with what {@code toACase} asks of the row put on it: what a row
         *  composed for the case has to satisfy of the input. */
        public WayToTheBorder statesToACase(CaseWay toACase) {
            List<OnTheWay> entries = new ArrayList<>(states().onTheWay());
            entries.addAll(toACase.puts());
            return WayToTheBorder.forArrival(entries);
        }

        /**
         * What the same conditions ask of the answers a row stands the dependencies in with, which
         * is the other half of what such a row has to be.
         *
         * <p>Two accounts because a row writes at a position and stands a dependency in, and what a
         * search may assume about the one is not what it may pin the other to.
         */
        public AnswersDemanded demands() {
            List<AnswerDemand> stated = new ArrayList<>();
            List<DemandGap.Unstated> declined = new ArrayList<>();
            Set<ConditionOccurrence> takenUp = new LinkedHashSet<>();
            for (RuleStep each : steps) {
                stated.addAll(each.demands().stated());
                declined.addAll(each.demands().declined());
                takenUp.addAll(each.demands().takenUp());
            }
            return stated.isEmpty() && declined.isEmpty()
                    ? AnswersDemanded.NOTHING : new AnswersDemanded(stated, declined, takenUp);
        }

        /**
         * Which copies of the model's code each thing on this way was read off: what each step
         * says of its own statements, all of them together.
         *
         * <p>Carried by the steps from where each condition was read, and never worked out from
         * where a step is seen: the construct a run through a condition is seen at is one, and
         * the constructs what it states was read off may be several, in other calls.
         */
        public SaidOnTheWay saidOnTheWay() {
            SaidOnTheWay out = SaidOnTheWay.NONE;
            for (RuleStep each : steps) {
                out = out.and(each.said());
            }
            return out;
        }
    }

    /**
     * A way through the body no rule past which is owed a row, proved, and what the proof says the
     * way is.
     *
     * <p>Three answers, and a reader of these is told which it holds. A way no input takes is one
     * no run goes down, and there is nothing to do about it. A way every run of which stops at a
     * construction is one runs go down and every one of them is refused: the conditions on it leave
     * inputs, and what the constructions on it are handed under them breaks their invariants. And a
     * way the proof could not tell between the two, because the figure of conditions taken in was
     * spent before the proof without a construction was answered: no input gets past the
     * constructions, and whether any input brings the conditions out is not known. All three leave
     * every rule past the way owed no row, since no run gets past it, and only the first is the
     * body being unreachable there; read as one, a body every run of which aborts along a way would
     * be said as a way nothing reaches, and a way nobody decided about as either.
     *
     * <p>The conditions the way consulted as it met them, which is a way and not a rule: the reading
     * stopped there, so it names the conditions the proof needed and none past them. Every rule that
     * goes on from it consults these as it did, and is no rule a run gets to the end of — this one
     * proof is the account of all of them, and none of them is counted as a rule.
     */
    public sealed interface Excluded permits ImpossiblePath, EveryRunStops, UndecidedAtAFigure {

        /** What the way consulted and went through, and where a run down it would be seen. */
        Ruled way();

        /** What leaves no input getting past everything on it. */
        NoInputTakesIt why();

        /**
         * Whether the proof stands for {@code other}: it consulted every condition this way did as
         * this way did, and goes through every construction this way does, so whatever left this
         * way no input leaves {@code other} none.
         */
        default boolean standsFor(Ruled other) {
            return consultedAsIn(other.rule()) && other.passed().containsAll(way().passed());
        }

        /** The same, of a rule along a way through no construction. */
        default boolean standsFor(DecisionRule rule) {
            return consultedAsIn(rule) && way().passed().isEmpty();
        }

        /** Whether the way consulted {@code rule}'s conditions as {@code rule} did. */
        private boolean consultedAsIn(DecisionRule rule) {
            return way().rule().consulted().entrySet().stream().allMatch(each ->
                    each.getValue().equals(rule.consulted().get(each.getKey())));
        }
    }

    /**
     * A way through the body no input takes, proved: what its conditions state leaves no input,
     * whatever it goes through.
     *
     * @param way what the way consulted, and where a run down it would have been seen doing so
     * @param why what leaves no input there
     */
    public record ImpossiblePath(Ruled way, NoInputTakesIt why) implements Excluded {

        public ImpossiblePath {
            Objects.requireNonNull(way, "a way no input takes is some way");
            Objects.requireNonNull(why, "a way no input takes is proved to be one");
        }
    }

    /**
     * A way through the body every run of which stops at a construction, proved.
     *
     * <p>Some input brings out the conditions on it as the way does — no proof is had of them
     * alone — and none of those gets past every clause of a construction the proof keeps
     * ({@link Ruled#passed}): each is a construction a run along the way reaches, or one stopped
     * before it reaches, and what it is handed there breaks the clause kept. No rule past
     * it is owed a row, since no run gets past; and it is not unreachable, since every one of those
     * runs got as far as the construction.
     *
     * <p>A fact about the model, and nothing a row is owed for: the same kind of fact as a
     * comparison every run reaching which stops in an operation it is read through
     * ({@link BlockReason.ComparisonAnswersNowhere}), which states nothing
     * on either side because no run gets past it. No row can answer the way, since every row down
     * it stops too. What is wrong is the body, building a value nothing it is handed there can be.
     * This is a fact about the model that stands by itself: the check of the model's invariants
     * may or may not report the same construction as well, and this neither depends on that
     * report nor stands in for it. The account says the way and where its runs stop, and leaves
     * the verdict where the rules put it.
     *
     * <p>Some construction the proof keeps names the clause it is held to. One whose invariant was
     * not reached states only that it was not read, which proves no contradiction, so a proof had
     * with it is had without it and a least proof answered in full never keeps it
     * ({@link ClauseOfAConstruction}). A least proof keeping nothing else stopped at the figure, and
     * is {@link UndecidedAtAFigure}.
     *
     * @param way what the way consulted and the constructions the proof keeps, never none of them,
     *            and some of them held to a clause
     * @param why what leaves no input getting past them
     */
    public record EveryRunStops(Ruled way, NoInputTakesIt why) implements Excluded {

        public EveryRunStops {
            Objects.requireNonNull(way, "a way every run of which stops is some way");
            Objects.requireNonNull(why, "a way every run of which stops is proved to be one");
            if (way.passed().stream().noneMatch(each ->
                    each.clause() instanceof ClauseOfAConstruction.Held)) {
                throw new IllegalArgumentException("a way every run of which stops goes through a"
                        + " construction held to a clause the way's inputs break: " + way);
            }
        }

        /** The clauses of the constructions every run along the way stops at one of. */
        public List<PassedConstruction> stoppedAt() {
            return way.passed();
        }
    }

    /**
     * A way through the body no input gets past, where the proof could not say whether any input
     * takes it at all: the figure of conditions taken in was spent before a proof without one of
     * the constructions on it was answered.
     *
     * <p>Either of the other two. Some input may bring out the conditions on the way, and then every
     * such run stops at one of the constructions kept, which is the body building a value nothing
     * it is handed there can be — or none does, and then the way is unreachable. No rule past it
     * is owed a row either way, since the proof that no input both takes the conditions and gets
     * past the constructions was had in full. What the figure left open is which of the two the
     * way is, and that changes no verdict.
     *
     * @param way    what the way consulted and the constructions still in the proof, never none
     *               of them
     * @param why    what leaves no input getting past them
     * @param figure the figure the proof stopped at, as it stood there
     */
    public record UndecidedAtAFigure(Ruled way, NoInputTakesIt why, Figure figure)
            implements Excluded {

        public UndecidedAtAFigure {
            Objects.requireNonNull(way, "a way left undecided is some way");
            Objects.requireNonNull(why, "no input gets past a way left undecided, proved");
            Objects.requireNonNull(figure, "a proof cut short was cut short at some figure");
            if (way.passed().isEmpty()) {
                throw new IllegalArgumentException("a way proved of its conditions alone is one no"
                        + " input takes: " + way);
            }
        }

        /** The clauses of the constructions every run along the way would stop at one of, were
         *  any input to take it. */
        public List<PassedConstruction> stoppedAt() {
            return way.passed();
        }
    }

    /** The ways no input takes, of {@link #excluded}. */
    public List<ImpossiblePath> impossible() {
        return excluded.stream().filter(ImpossiblePath.class::isInstance)
                .map(ImpossiblePath.class::cast).toList();
    }

    /** The ways every run of which stops at a construction, of {@link #excluded}. */
    public List<EveryRunStops> everyRunStops() {
        return excluded.stream().filter(EveryRunStops.class::isInstance)
                .map(EveryRunStops.class::cast).toList();
    }

    /** The ways a proof cut short at a figure did not tell between the other two, of
     *  {@link #excluded}. */
    public List<UndecidedAtAFigure> undecided() {
        return excluded.stream().filter(UndecidedAtAFigure.class::isInstance)
                .map(UndecidedAtAFigure.class::cast).toList();
    }

    /**
     * One rule and every place the body states it.
     *
     * <p>What is owed a row, settled, found or counted is the rule, and the places are where it
     * stands. A row that takes the rule at any of them takes the rule, so what a reader asks of the
     * rule is asked over all of them together: the rows it asks for are the rows of every place, and
     * one place's answer is not the rule's. Read one place at a time, a rule stated twice would be
     * judged by whichever place was met first or last.
     *
     * @param rule        the rule
     * @param occurrences every place it is stated, in the order the reading met them. Never empty
     */
    public record Stated(DecisionRule rule, List<Ruled> occurrences) {

        public Stated {
            occurrences = List.copyOf(occurrences);
            if (occurrences.isEmpty()) {
                throw new IllegalArgumentException("a rule is stated somewhere: " + rule);
            }
            for (Ruled each : occurrences) {
                if (!each.rule().equals(rule)) {
                    throw new IllegalArgumentException("the places of one rule are of that rule: "
                            + rule + " with " + each.rule());
                }
            }
        }

        /**
         * The place a reader is shown, which is where to look and not where the rule is: the
         * conditions are the rule's, and every place states them alike.
         */
        public Ruled display() {
            return occurrences.getFirst();
        }
    }

    /**
     * Every rule once, with every place it is stated, in the order the reading first met each.
     *
     * <p>The one grouping of the places of a rule. A reader that asks about the rule — what it is
     * owed, what settles it, whether every row of it aborts — asks this, and only a reader that
     * asks about a place reads {@link #found} itself.
     */
    public List<Stated> stated() {
        Map<DecisionRule, List<Ruled>> byRule = new LinkedHashMap<>();
        for (Ruled each : found) {
            byRule.computeIfAbsent(each.rule(), _ -> new ArrayList<>()).add(each);
        }
        List<Stated> out = new ArrayList<>();
        byRule.forEach((rule, occurrences) -> out.add(new Stated(rule, occurrences)));
        return List.copyOf(out);
    }

    /** The rules themselves, each once, for a reader that asks what the body decides and not
     *  where. */
    public List<DecisionRule> rules() {
        return stated().stream().map(Stated::rule).toList();
    }

    /** Whether the reading wrote down every way through the body, or would not hold them apart. */
    public sealed interface Enumeration {

        /** Every way was written down. */
        record Complete() implements Enumeration {}

        /**
         * The reading would not hold this many ways apart, so the rules here are none of the
         * body's rather than some of them.
         *
         * <p>Which is what the reading of the ways answers: a list with ways missing from it reads
         * as a whole one, so where it will not hold them all it holds none. A reader is owed the
         * figure and not a shorter list.
         *
         * @param figure which figure it reached, so that a reader is told what to raise
         */
        record StoppedAtAFigure(CompositionBudget figure) implements Enumeration {}
    }

    /**
     * The decision {@code body} states, read under {@code reads}.
     *
     * <p>Whose body it is is asked for, because a rule is reported as a rule of a behavior and a
     * condition takes its name from the reading of one.
     *
     * <p>A distinction the body draws on what a dependency answered is one a row can write for, and
     * the same call to anything else is a value the model computes; which calls are which is
     * {@code reads}'s ({@link InputReads#standsIn}).
     */
    public static DecisionReading of(String behavior, AnalysisBody analysis, InputReading read,
                                     InputReads reads) {
        return of(behavior, analysis, read, reads, CaseCandidates.NEARBY);
    }

    /**
     * The same, with the ways to the cases a search draws made for the candidates {@code
     * candidates} says, over the places {@code read} has read.
     */
    public static DecisionReading of(String behavior, AnalysisBody analysis, InputReading read,
                                     InputReads reads, CaseCandidates candidates) {
        Core body = analysis.core();
        // The conditions of this body take their names here, and one register serves every scope: a
        // condition met under a binding and the same condition met outside it are one condition.
        ConditionNumbering numbering = new ConditionNumbering(read.symbols().module(), behavior,
                ConditionOccurrence.Reading.DECIDING);
        // What a build of a value comes to is what its template does: a value that never answers
        // leaves nothing after its build reached. What is inside the template is not counted as a
        // way of this body — a value takes no input, so it is no rule a row can be written for.
        WaysNoInputTakes proved = new WaysNoInputTakes();
        DecisionNaming naming = new DecisionNaming(meanings(read, candidates), reads, numbering,
                PATHS_READ.maximum(), proved);
        ValueArrivals<DecisionPath> arrivals = ValueArrivals.ofBodyWhereTheOperationsStand(body,
                naming, new AnOperationsTruthComesOutAsItCan(reads, read),
                analysis.templates()::bodyOf);
        if (!(arrivals.waysAt(body) instanceof Paths.Held<DecisionPath> held)) {
            return new DecisionReading(behavior, List.of(), proved.leastOfThem(),
                    new Enumeration.StoppedAtAFigure(PATHS_READ), Map.of());
        }
        // Every way the reading ends at is asked as well, since a way can come to its conditions
        // without one join that put them together. And a rule past a way no input takes is not held
        // beside the proof, however the reading came to it: the proof stands for it.
        List<Arrival<DecisionPath>> arrived = held.arrivals().stream()
                .filter(way -> !naming.takenByNoInput(way.path())).toList();
        List<Excluded> excluded = proved.leastOfThem();
        List<Ruled> found = new ArrayList<>();
        for (Arrival<DecisionPath> way : arrived) {
            Ruled ruled = new Ruled(way.path().rule(), way.path().steps(), way.isComplete(),
                    way.path().passed());
            if (excluded.stream().noneMatch(each -> each.standsFor(ruled))) {
                found.add(ruled);
            }
        }
        return new DecisionReading(behavior, found, excluded, new Enumeration.Complete(),
                numbering.metAt());
    }

    /** What this body's conditions decide, made once for the whole reading of it. */
    private static DecisionMeanings meanings(InputReading read, CaseCandidates candidates) {
        return new DecisionMeanings(new ConditionMeanings(read),
                WhatAnAnswerTakesUp.of(read).subjects(), candidates);
    }
}
