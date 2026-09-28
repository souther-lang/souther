package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What an exponent stands for on each side of the line is read from the exponent itself, and never from
 * a negation held in a {@code long}.
 *
 * <p>The least long is its own negation, so {@code -exponent} says nought's opposite there: a value at
 * that exponent read below the line through a long would have nothing below it. The two readings are
 * asked at the ends of the range, where that shows.
 */
class AnExponentIsReadAboveOrBelowTheLineWithoutBeingNegatedAsALongTest {

    private static final BigInteger TWO_TO_THE_SIXTY_THIRD = BigInteger.ONE.shiftLeft(63);

    @Test
    void theLeastLongStandsBelowTheLineByItsTrueSize() {
        assertEquals(TWO_TO_THE_SIXTY_THIRD, ExactArithmetic.belowTheLine(Long.MIN_VALUE));
        assertEquals(BigInteger.ZERO, ExactArithmetic.aboveTheLine(Long.MIN_VALUE));
    }

    @Test
    void theGreatestLongStandsAboveTheLineByItself() {
        assertEquals(BigInteger.valueOf(Long.MAX_VALUE), ExactArithmetic.aboveTheLine(Long.MAX_VALUE));
        assertEquals(BigInteger.ZERO, ExactArithmetic.belowTheLine(Long.MAX_VALUE));
    }

    @Test
    void anExponentStandsOnOneSideOnly() {
        for (long exponent : new long[] {-7, -1, 0, 1, 7}) {
            assertEquals(BigInteger.valueOf(Math.max(exponent, 0)), ExactArithmetic.aboveTheLine(exponent));
            assertEquals(BigInteger.valueOf(Math.max(-exponent, 0)), ExactArithmetic.belowTheLine(exponent));
        }
    }

    /** And the one operation that wants the negation as an exponent says so rather than wrapping. */
    @Test
    void theNegationAsAnExponentIsRefusedForTheLeastLong() {
        assertThrows(ExactRangeExceeded.class, () -> ExactArithmetic.negated(Long.MIN_VALUE));
        assertEquals(Long.MAX_VALUE, ExactArithmetic.negated(-Long.MAX_VALUE));
    }
}
