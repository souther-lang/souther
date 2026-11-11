package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A rounding, a narrowing to a whole number and a quotient at a scale answer wherever the answer
 * itself has a place, whatever a {@code BigDecimal} would have built on the way to it (spec
 * §an-operation-refuses-only-what-its-own-answer-has-no-place-for). A value at the far end of a
 * {@code BigDecimal}'s scales rounds to nought, or one step from it, and a {@code BigDecimal}
 * brought to that scale builds the power of ten between the two and has no room for it.
 */
class ADecimalNarrowedToAPlaceItsAnswerHasAnswersTest {

    /** One at the far end of the scales a {@code BigDecimal} keeps. */
    private static final BigDecimal TINY = new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE);

    @Test
    void aRoundingOfAValueFarNearerNoughtThanItsScaleAnswers() {
        assertEquals(new BigDecimal("0"), DecimalMath.round(0, HALF_UP.INSTANCE, TINY));
        assertEquals(new BigDecimal("0.01"), DecimalMath.round(2, UP.INSTANCE, TINY));
        assertEquals(new BigDecimal("-0.01"), DecimalMath.round(2, FLOOR.INSTANCE, TINY.negate()));
    }

    @Test
    void aWholeNumberOfAValueFarNearerNoughtThanItsScaleAnswers() {
        assertEquals(0L, DecimalMath.toInt(HALF_UP.INSTANCE, TINY));
        assertEquals(1L, DecimalMath.toInt(CEILING.INSTANCE, TINY));
    }

    @Test
    void aQuotientOfAValueFarNearerNoughtThanItsScaleAnswers() {
        assertEquals(new BigDecimal("0.00"),
                DecimalMath.divide(TINY, new BigDecimal("3"), 2, HALF_UP.INSTANCE));
        assertEquals(new BigDecimal("0.01"),
                DecimalMath.divide(TINY, new BigDecimal("3"), 2, UP.INSTANCE));
    }

    /** Control: where the answer itself is past what a {@code BigDecimal} writes, the run is
     *  still short of room. */
    @Test
    void anAnswerWithNoPlaceIsStillShortOfRoom() {
        BigDecimal huge = new BigDecimal(BigInteger.ONE, Integer.MIN_VALUE + 1);
        assertThrows(OutOfRoom.class, () -> DecimalMath.round(0, HALF_UP.INSTANCE, huge));
    }
}
