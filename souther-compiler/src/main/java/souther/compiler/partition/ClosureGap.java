package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.RuleWithoutALine;

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

    /**
     * A rule of the model a reader stopped on. The rule says which measures that costs
     * ({@link BlockReason.RuleWithoutLineReason#leavesShort}).
     *
     * <p>Only a rule this compiler got partway through. A rule read from end to end that draws no
     * line leaves no measure short of anything — that is what its half of the reasons answers, for
     * every one of them and not case by case — so it is not a gap in what was measured and there is
     * nothing here for it to be counted as. `MeasureClosure` asks the reason before building one of
     * these, and this refuses what that question would have had to let through.
     */
    record RuleUnread(RuleWithoutALine rule) implements ClosureGap {

        public RuleUnread {
            if (!(rule.why() instanceof BlockReason.RuleReadingStopped)) {
                throw new IllegalArgumentException(
                        "a rule read to the end leaves no measure short: " + rule.why());
            }
        }
    }

    /**
     * A question the rules written about one position raise that nothing answered.
     *
     * <p>A clause's, and never a comparison's. A comparison raises a question exactly where the
     * reading of it reached a line, and that line is the answer — so a comparison either yields
     * both or yields neither and records what stopped its reading. Which is why a comparison's
     * incompleteness reaches this only as {@link RuleUnread}.
     */
    record QuestionUnanswered(souther.compiler.inputs.StandingQuestion question)
            implements ClosureGap {}

    /**
     * A position whose rules nothing enumerated. It raises no question, so it cannot be short of
     * one — which is why it is a gap of its own and not one of the two above.
     *
     * <p><b>Not every way the rules go unread reaches this.</b> A handing over left standing because
     * the walk could not go into the position is the same stop {@link PositionNotReachedInto}
     * reports, and it is written there once. Which of the ways this is comes off the arm the reading
     * settled and never off what else was found at the path
     * ({@link souther.compiler.inputs.RulesLeftUnread}): a position the reading entered and lost a
     * clause of its own is an independent finding, and a fold on the path would take it with the
     * other (issue #1084).
     */
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
     *
     * <p><b>{@code at} names the axis carrying the fact, and the position is that axis's path.</b>
     * The two come apart: a {@code Map} nothing can be read into, under a rule about its size, is
     * measured at the size and the axis is named for that term. So this is not "the identity of the
     * position that was blocked" — it is the axis a reader holding these numbers is being told
     * something about, which is the one thing a gap beside a measurement is for. Keyed by the
     * position instead, this arm and {@link RulesNotReached} would name a behavior's findings in two
     * vocabularies.
     *
     * <p>Written from {@link souther.compiler.inputs.BlockedDescent} and never from what the axis is
     * still waiting on. A position something answered for keeps no continuation, and was still never
     * entered.
     */
    record PositionNotReachedInto(AxisId at, BlockReason.AboutThePosition why) implements ClosureGap {}
}
