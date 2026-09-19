package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That a decimal's scale reaches a rational as an exponent, and that what is done with the value
 * afterwards does not build the power the scale names.
 *
 * <p>The scales here are ones whose power of ten has no representation a machine holds — a scale of a
 * billion asks for a number of some four hundred megabytes — so a step that built one would not
 * finish rather than finishing slowly. That is the positive control: every assertion below is reached
 * only by an implementation that left the scale an exponent.
 */
class ARationalsScaleIsAnExponentAndNotDigitsTest {

    /** A decimal written as one digit and a scale, which is eleven characters and not a billion. */
    private static final BigDecimal COMPACT = new BigDecimal(BigInteger.ONE, 1_000_000_000);

    @Test
    void aScaleBecomesTwoExponentsAndNoDigits() {
        Rational taken = Rational.of(COMPACT);
        assertEquals(BigInteger.ONE, taken.numerator());
        assertEquals(BigInteger.ONE, taken.denominator());
        assertEquals(-1_000_000_000, taken.twos());
        assertEquals(-1_000_000_000, taken.fives());
    }

    @Test
    void multiplyingAndDividingMoveTheExponentsAndBuildNothing() {
        Rational taken = Rational.of(COMPACT);
        Rational squared = taken.times(taken);
        assertEquals(-2_000_000_000, squared.twos());
        assertEquals(-2_000_000_000, squared.fives());
        assertEquals(Rational.ONE, taken.dividedBy(taken));
        assertEquals(taken, squared.dividedBy(taken));
        assertEquals(1_000_000_000, taken.reciprocal().twos());
    }

    /**
     * Every decimal has one of these, including the one whose scale has no positive counterpart.
     *
     * <p>The widening is a rule and not a range this type happens to cover: a scale is thirty-two bits
     * and enters as its negation, so an exponent of the same width would refuse the least scale there
     * is. This is the value that says the two widths are not the same question.
     */
    @Test
    void theLeastScaleThereIsWidensLikeAnyOther() {
        Rational taken = Rational.of(new BigDecimal(BigInteger.ONE, Integer.MIN_VALUE));

        assertEquals(2147483648L, taken.twos());
        assertEquals(2147483648L, taken.fives());
        assertEquals(BigInteger.ONE, taken.numerator());
    }

    /** An exponent is sixty-four bits, and a product asking for more of it aborts rather than
     *  answering about a value it cannot hold. */
    @Test
    void anExponentPastWhatIsHeldAborts() {
        Rational far = new Rational(BigInteger.ONE, BigInteger.ONE, Long.MAX_VALUE, 0);

        assertThrows(ConstraintViolation.class, () -> far.times(far));
    }

    /** And a product whose exponents merely add is exact, however far past a scale's own width they
     *  run — which is the control for the abort above. */
    @Test
    void aProductPastWhatAScaleHoldsIsStillExact() {
        Rational taken = Rational.of(COMPACT);
        Rational squared = taken.times(taken);

        assertEquals(-2_000_000_000L, squared.twos());
        assertEquals(-4_000_000_000L, squared.times(squared).twos());
    }

    /** A millionth of a millionth against one: the brackets on the two logs are nowhere near each
     *  other, so the answer comes from the exponents. */
    @Test
    void aComparisonIsDecidedFromTheExponentsWhereTheValuesAreApart() {
        Rational taken = Rational.of(COMPACT);
        assertEquals(Integer.valueOf(-1), taken.magnitudeFromBounds(Rational.ONE));
        assertTrue(taken.compareTo(Rational.ONE) < 0);
        assertTrue(Rational.ONE.compareTo(taken) > 0);
        assertTrue(taken.compareTo(taken.negated()) > 0);
        assertEquals(0, taken.compareTo(Rational.of(COMPACT)));
    }

    /**
     * And where they are close the brackets settle nothing, whatever the exponents are.
     *
     * <p>Two values within a factor of two of one another overlap however large they are, so the
     * bracket is a way of answering cheaply where the values are apart and not a bound on what
     * answering costs. The comparison of this pair is not asked for here: what it would build is the
     * billion-bit number the assertion above says the cheap path avoids.
     */
    @Test
    void closeValuesAreNotSettledByTheBracketsHoweverLargeTheyAre() {
        Rational aPower = new Rational(BigInteger.ONE, BigInteger.ONE, 1_000_000_000, 0);
        Rational halfAgainBelowIt =
                new Rational(BigInteger.valueOf(3), BigInteger.ONE, 999_999_999, 0);
        assertNull(aPower.magnitudeFromBounds(halfAgainBelowIt));
        assertNull(halfAgainBelowIt.magnitudeFromBounds(aPower));

        // the same bracket decides a pair that is merely small and far apart, which is what says the
        // two answers above are the overlap and not a bracket that never decides anything
        assertEquals(Integer.valueOf(-1), Rational.of(1).magnitudeFromBounds(Rational.of(1000)));
    }

    /** A value too large to read is described rather than spelled, and the description is the size of
     *  what is stored. */
    @Test
    void aValueTooLargeToSpellIsDescribed() {
        assertEquals("1/1×2^-1000000000×5^-1000000000", Rational.of(COMPACT).toString());
        assertEquals("1/2", Rational.of(BigInteger.ONE, BigInteger.TWO).toString());
        assertEquals("2", Rational.of(4).dividedBy(Rational.of(2)).toString());
        assertEquals("-1/3", Rational.of(-1).dividedBy(Rational.of(3)).toString());
    }
}
