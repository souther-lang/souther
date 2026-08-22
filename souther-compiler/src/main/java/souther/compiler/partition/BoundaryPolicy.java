package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;

/**
 * Whether the rules of a model are read off one comparison, and why not where they are not.
 *
 * <p><b>The rule, said in what a behavior does rather than in what a body looks like.</b> A
 * comparison is a boundary rule where its truth is on a live flow to what the behavior answers with,
 * and where one run passes it at most once. Nothing about the construct it is written in is part of
 * that. A comparison tested by an {@code if}, given a name a line above the fork that tests it,
 * returned as the behavior's answer, or written into a field of the answer's data is one rule put to
 * four uses, and a model divides its input at the same value in all four — so naming a truth is not
 * a statement about what a model divides, and neither is spelling one out.
 *
 * <p>It was written as {@code directly under a fork, through &&  and ||} because a fork was for a
 * long time the only thing that could measure a comparison: reaching an arm was the evidence that
 * the comparison ran. That made one sentence do two jobs — whether the comparison can be measured,
 * and whether the model states anything by it — and the two came apart the day a comparison got a
 * site of its own. The measurement moved to the comparison and the policy did not, so a
 * meaning-preserving rewrite moved the partition.
 *
 * <p><b>A policy over {@link souther.compiler.coverage.ComparisonCatalog}</b> and not a second
 * account of what a comparison is. The catalog says what the bodies hold; this decides which of
 * those a line is drawn on, and the two are different questions with different answers. Kept apart
 * because the first is a fact about the source and the second is a decision about what a model
 * divides — and while they were one walk, the decision was being made by whatever the numbering
 * happened to reach.
 *
 * <p><b>A decision and not a walk.</b> Where a comparison is written and what is in force there is
 * {@link ComparisonReadings}'s, asked once for the whole body; this is what that walk asks at each
 * of them. Holding a walk of its own, this was one of two readings threading the same {@code let}
 * rule through the same tree to answer different halves of one question.
 *
 * <p>What is not answered here is what reaching an arm of a fork proves about a comparison under it.
 * Under {@code A && (B || C)} the arms tell those three apart — the arm the whole condition holds on
 * proves {@code A} ran and {@code B} ran, and proves nothing about {@code C} — and no measure asks: a
 * row meets a line by lighting the comparison's own probe, which is a fact the comparison records for
 * itself. It is a relation between a comparison and one use of its truth, so a comparison consumed by
 * two forks has two answers and one consumed by none has no answer at all. Anything modelling it
 * belongs where the uses are, not here and not on the origin.
 */
final class BoundaryPolicy {

    /** What this policy says about one comparison of the body. */
    sealed interface Standing {

        /** The comparison this is about, whichever answer it got. */
        Core.Binary comparison();

        /** A line is drawn on it. */
        record DrawsALine(Core.Binary comparison) implements Standing {}

        /** No line is drawn on it, and this is which of the reasons it is. */
        record DrawsNone(Core.Binary comparison, NotABoundary why) implements Standing {}
    }

    /**
     * What {@code comparison}'s standing is, where it stands.
     *
     * <p>The reason about the model is said first. A comparison the behavior's answer does not turn
     * on is not a boundary whichever way it could have been measured, and a reader told instead that
     * its outcome cannot be attributed to a row would go looking for a way to attribute it.
     *
     * <p>Where the comparison stands and what its names point at are not arguments to this. A
     * decision that took the reading only to hand it back was a second place holding it, and the
     * walk that has it is {@link ComparisonReadings}.
     *
     * @param live whether what is computed at this position is read on the way to what the behavior
     *             answers with, which is {@link LiveFlow}'s answer carried down the walk
     */
    static Standing standingOf(Core.Binary comparison, CoverageSites.Plan plan, boolean live) {
        if (!live) {
            return new Standing.DrawsNone(comparison, NotABoundary.NOTHING_READS_IT);
        }
        // Meeting a line takes getting the comparison to answer, and whether it answered is what a
        // site records — so a comparison with no site is one no row could ever be shown to have
        // reached, and a border on it would owe a row nothing can measure.
        if (plan.comparisonAt(comparison).isEmpty()) {
            return new Standing.DrawsNone(comparison, NotABoundary.NOTHING_RECORDS_IT);
        }
        // A recording holds that a place was passed and not how many times, so two outcomes of one
        // comparison in one run cannot be told from two rows' outcomes.
        if (plan.mayRepeat(comparison)) {
            return new Standing.DrawsNone(comparison, NotABoundary.REPEATED_IN_ONE_RUN);
        }
        return new Standing.DrawsALine(comparison);
    }

    private BoundaryPolicy() {}
}
