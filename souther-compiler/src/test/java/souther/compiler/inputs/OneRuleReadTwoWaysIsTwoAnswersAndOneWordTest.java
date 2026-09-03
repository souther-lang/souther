package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ReportedReason;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.values.UnreadReason;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * One rule, two readings, two answers — and one word for a reader of the document.
 *
 * <p>{@code a < b} is where this is settled. The reading that turns clauses into lines takes it in
 * whole and places no line, and no measure is short of anything on its account. The reading that
 * turns clauses into sets of values gets nothing it can hold from the same rule, so what it
 * arrived at is an upper bound over a position whose values this compiler cannot state. Both are
 * true, and they are opposite sentences about this compiler.
 *
 * <p>So which half a reason is in is not a property of the rule. It is a property of the rule and
 * the reading together, and the two readings have their own reasons for the same rule. Held as one
 * reason on the grounds that two vocabularies must not come to different words for one stop, the
 * value reading's account said what the line reading's says — that the rule was read and nothing is
 * missing — over a position it had read nothing about.
 *
 * <p>The word is not what was ever shared. A document promises its reader which kind of thing
 * stopped the derivation, and both of these are one kind of thing out there: the projection sends
 * them to one word, which is asserted here beside the split so that the two cannot drift.
 */
class OneRuleReadTwoWaysIsTwoAnswersAndOneWordTest {

    /** What the reading of lines makes of it: read to the end, and no line either side. */
    private static final BlockReason.ComparisonBetweenPositions THE_LINE_READING =
            new BlockReason.ComparisonBetweenPositions();

    /** And what the reading of values makes of the same rule. */
    private static final BlockReason.RuleReadingStopped THE_VALUE_READING =
            BlockReason.ofARuleTheValueReadingLeft(UnreadReason.RELATES_TWO_POSITIONS);

    /**
     * The line reading finished, so nothing is owed on its account.
     *
     * <p>That it is no {@link BlockReason.ReadingStopReason} is not asserted here, and cannot be:
     * the two are disjoint under the seal, so javac refuses an {@code instanceof} between them as
     * one that can never hold. A test would be the weaker statement of the two — this one cannot be
     * handed to a caller asking what stopped a reading in any program that compiles.
     */
    @Test
    void theLineReadingReadItToTheEnd() {
        assertInstanceOf(BlockReason.ReadToEndWithoutLine.class, THE_LINE_READING);
    }

    /**
     * The value reading stopped, and every answer that reading gives is one.
     *
     * <p>What is held at a position is a set of its own values, and a rule about how it stands
     * against another position is not one. So the values are an upper bound: this compiler fell
     * short, whatever the reading beside it managed with the same rule.
     *
     * <p>And the same exclusion holds the other way, under the same seal: this answer cannot be
     * handed to a caller asking what a rule read from end to end left, so it cannot say that
     * nothing is missing.
     */
    @Test
    void theValueReadingStoppedOnIt() {
        assertInstanceOf(BlockReason.ReadingStopReason.class, THE_VALUE_READING);
    }

    /** And a reader of the document meets one word, which is what the two were made one for. */
    @Test
    void theDocumentWritesOneWordForBoth() {
        assertEquals(UndividedPosition.Reason.UNSUPPORTED_PARTITION_SHAPE,
                ReportedReason.of(THE_LINE_READING));
        assertEquals(UndividedPosition.Reason.UNSUPPORTED_PARTITION_SHAPE,
                ReportedReason.of(THE_VALUE_READING));
    }

    /**
     * The reading that never arrived at a position's rules is refused rather than answered.
     *
     * <p>It is holding no rule for an answer about one to be about, which is what the reasons about
     * a position are beside these for.
     */
    @Test
    void aReadingThatReachedNoRuleNamesNone() {
        assertInstanceOf(BlockReason.AboutThePosition.class,
                BlockReason.of(UnreadReason.NOT_REACHED));
        assertThrows(IllegalArgumentException.class,
                () -> BlockReason.ofARuleTheValueReadingLeft(UnreadReason.NOT_REACHED));
    }
}
