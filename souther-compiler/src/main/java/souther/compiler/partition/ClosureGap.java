package souther.compiler.partition;

import souther.compiler.check.RuleAccounting;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.UnreadRule;

/**
 * One thing that stopped a measure's reading of the model from running out.
 *
 * <p>What {@link MeasureClosure} used to answer with a boolean. Whether the reading ran out and what
 * was left of it when it did not are one question asked twice, and only the first of them had a
 * value: a measure that came back weaker than complete said so and nothing said why, so every reader
 * that wanted the why rebuilt it from the lists kept beside the measure (issue #953).
 *
 * <p><b>The fact itself, not a code and a name for what it is about.</b> Each arm holds what the
 * reader that found it produced. Written as a code and a subject the two would have to be taken
 * apart again by whoever wanted the rule, and a subject wide enough to hold a rule, a position and
 * an omitted axis is one every reader has to guess the shape of.
 *
 * <p>Which measures each of these costs is not asked here. That is
 * {@link MeasureClosure#of}'s to decide and the answers differ — a rule relating two positions
 * leaves neither measure short, and an omitted axis leaves the border measure short only where it
 * was carrying a line.
 */
public sealed interface ClosureGap {

    /** A rule of the model that a reader set aside. The rule says which measures that costs
     *  ({@link BlockReason.AboutARule#leavesShort}). */
    record RuleUnread(UnreadRule rule) implements ClosureGap {}

    /** A question the rules written about one position raise that nothing answered. */
    record QuestionUnanswered(AxisId at, RuleAccounting.Unanswered question) implements ClosureGap {}

    /** The same, for a question a body's comparison raised. It is filed at a path rather than at an
     *  axis because a comparison is read where it is written and not at a position that was kept. */
    record ComparisonUnanswered(TermPath at, RuleAccounting.Unanswered question)
            implements ClosureGap {}

    /** A position whose rules nothing enumerated. It raises no question, so it cannot be short of
     *  one — which is why it is a gap of its own and not one of the two above. */
    record RulesNotReached(AxisId at) implements ClosureGap {}

    /**
     * A position the walk could not reach into, with what the structural reading found instead.
     *
     * <p>The one arm for a position with no rule to name. There were two for a while — this and a
     * {@code PositionBlocked} taking {@code PositionReadingBlocked}, which is the same fact keyed by
     * path rather than by axis. It was written from the list {@code PartitionEvidence} keeps beside
     * the measures rather than from what {@link MeasureClosure#of} finds, so nothing ever built one:
     * an arm taken from a second representation of a fact, which is the mistake #953 is about, in
     * miniature.
     */
    record PositionNotReachedInto(AxisId at, BlockReason.AboutThePosition why) implements ClosureGap {}

    /** A position dropped past the axis limit, with what dropping it cost. */
    record AxisOmitted(Partitions.OmittedAxis axis) implements ClosureGap {}
}
