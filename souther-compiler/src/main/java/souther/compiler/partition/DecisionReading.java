package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.flow.Arrival;
import souther.compiler.flow.Paths;
import souther.compiler.flow.ValueArrivals;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;

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
 * @param impossible  the ways no input takes, each where the proof was had and none narrower than
 *                    another, in the order the reading met them; the rules past each are in none of
 *                    {@code found}
 * @param enumeration whether every way was written down
 * @param metAt       where this reading met each condition it places itself, which is what a
 *                    report about one of them is sent to
 *                    ({@link ConditionReportAnchor.WhereTheReadingMetIt}). This reading's own: a
 *                    condition is named by the reading that met it, and the same name from
 *                    another reading is another condition
 */
public record DecisionReading(String behavior, List<Ruled> found, List<ImpossiblePath> impossible,
                              Enumeration enumeration, Map<ConditionOccurrence, Citation> metAt) {

    /** The figure this reading stops at, read here rather than written here. */
    private static final CompositionBudget PATHS_READ = CompositionBudget.PATHS_OF_A_DECISION_READ;

    public DecisionReading {
        found = List.copyOf(found);
        impossible = List.copyOf(impossible);
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
    public record Ruled(DecisionRule rule, List<RuleStep> steps, boolean whole) {

        public Ruled {
            steps = List.copyOf(steps);
        }

        /** Every condition the path consulted, said as what a run through it would be seen
         *  doing. */
        public List<ShownBy> shownBy() {
            return steps.stream().map(RuleStep::shown).toList();
        }

        /** The same conditions in the words a composer of a row works from, which is what a row
         *  standing in this rule would have to satisfy of the input. */
        public WayToTheBorder states() {
            return new WayToTheBorder(steps.stream()
                    .flatMap(each -> each.states().stream()).toList());
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
     * A way through the body no input takes, proved.
     *
     * <p>The conditions it consulted as the way met them, which is a way and not a rule: the reading
     * stopped there, so it names the conditions the proof needed and none past them. Every rule that
     * goes on from it consults these as it did, and is no rule a run takes — this one proof is the
     * account of all of them, and none of them is counted as a rule.
     *
     * @param way what the way consulted, and where a run down it would have been seen doing so
     * @param why what leaves no input there
     */
    public record ImpossiblePath(Ruled way, NoInputTakesIt why) {

        public ImpossiblePath {
            Objects.requireNonNull(way, "a way no input takes is some way");
            Objects.requireNonNull(why, "a way no input takes is proved to be one");
        }

        /** Whether the way consulted {@code rule}'s conditions as {@code rule} did, which makes
         *  the rule one past it. */
        public boolean standsFor(DecisionRule rule) {
            return way.rule().consulted().entrySet().stream().allMatch(each ->
                    each.getValue().equals(rule.consulted().get(each.getKey())));
        }
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
        Core body = analysis.core();
        // The conditions of this body take their names here, and one register serves every scope: a
        // condition met under a binding and the same condition met outside it are one condition.
        ConditionNumbering numbering = new ConditionNumbering(read.symbols().module(), behavior,
                ConditionOccurrence.Reading.DECIDING);
        // What a build of a value comes to is what its template does: a value that never answers
        // leaves nothing after its build reached. What is inside the template is not counted as a
        // way of this body — a value takes no input, so it is no rule a row can be written for.
        WaysNoInputTakes proved = new WaysNoInputTakes();
        DecisionNaming naming = new DecisionNaming(meanings(read), reads, numbering,
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
        List<ImpossiblePath> impossible = proved.leastOfThem();
        List<Ruled> found = new ArrayList<>();
        for (Arrival<DecisionPath> way : arrived) {
            DecisionRule rule = way.path().rule();
            if (impossible.stream().noneMatch(each -> each.standsFor(rule))) {
                found.add(new Ruled(rule, way.path().steps(), way.isComplete()));
            }
        }
        return new DecisionReading(behavior, found, impossible, new Enumeration.Complete(),
                numbering.metAt());
    }

    /** What this body's conditions decide, made once for the whole reading of it. */
    private static DecisionMeanings meanings(InputReading read) {
        return new DecisionMeanings(new ConditionMeanings(read),
                WhatAnAnswerTakesUp.of(read).subjects());
    }
}
