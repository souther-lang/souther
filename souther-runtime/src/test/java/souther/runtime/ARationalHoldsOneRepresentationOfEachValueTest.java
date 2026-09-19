package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

import static souther.runtime.Rational.STORED_BITS;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That a rational's stored form is decided by the value and not by the spelling it arrived in, and
 * that the arithmetic answers the number the operands make.
 *
 * <p>The canonical form is what lets {@link Values} ask one of these for its own equality and its own
 * hash, as it asks a generated data class. So the fields are asserted and not only the equality
 * derived from them: two representations of one value comparing equal is what a {@code Map} keyed by
 * one needs, and a test that only compared values would pass while the record held two forms of a
 * half and put them in two buckets.
 */
class ARationalHoldsOneRepresentationOfEachValueTest {

    private static Rational half() {
        return Rational.of(BigInteger.ONE, BigInteger.TWO);
    }

    @Test
    void everySpellingOfAHalfIsOneStoredForm() {
        Rational written = Rational.of(new BigDecimal("0.5"));
        for (Rational half : new Rational[] {
                half(),
                Rational.of(BigInteger.TWO, BigInteger.valueOf(4)),
                Rational.of(BigInteger.valueOf(5), BigInteger.TEN),
                written,
                Rational.of(new BigDecimal("0.50")),
                Rational.ONE.dividedBy(Rational.of(2)),
        }) {
            assertEquals(BigInteger.ONE, half.numerator());
            assertEquals(BigInteger.ONE, half.denominator());
            assertEquals(-1, half.twos());
            assertEquals(0, half.fives());
            assertEquals(written, half);
            assertEquals(written.hashCode(), half.hashCode());
        }
    }

    /** The factors ten is made of leave the fraction, and what is not one of them stays in it. */
    @Test
    void whatIsLeftOfTheFractionIsWhatTenIsNotMadeOf() {
        Rational third = Rational.of(BigInteger.ONE, BigInteger.valueOf(3));
        assertEquals(BigInteger.valueOf(3), third.denominator());
        assertEquals(0, third.twos());
        assertEquals(0, third.fives());

        // a sixth is a two and a three: one of them is an exponent and the other is not
        Rational sixth = Rational.of(BigInteger.ONE, BigInteger.valueOf(6));
        assertEquals(BigInteger.ONE, sixth.numerator());
        assertEquals(BigInteger.valueOf(3), sixth.denominator());
        assertEquals(-1, sixth.twos());
        assertEquals(0, sixth.fives());

        // and a twentieth is two twos and a five, with nothing left over
        Rational twentieth = Rational.of(BigInteger.ONE, BigInteger.valueOf(20));
        assertEquals(BigInteger.ONE, twentieth.denominator());
        assertEquals(-2, twentieth.twos());
        assertEquals(-1, twentieth.fives());
    }

    @Test
    void noughtHasOneFormWhateverItWasBuiltFrom() {
        assertEquals(Rational.ZERO, new Rational(BigInteger.ZERO, BigInteger.valueOf(7), 9, -4));
        assertEquals(BigInteger.ONE, new Rational(BigInteger.ZERO, BigInteger.TEN, 3, 3).denominator());
        assertEquals(0, new Rational(BigInteger.ZERO, BigInteger.TEN, 3, 3).twos());
        assertEquals(0, new Rational(BigInteger.ZERO, BigInteger.TEN, 3, 3).fives());
    }

    /** A sign belongs to the numerator, so a negative divisor does not make a second form of one
     *  value. */
    @Test
    void theSignIsTheNumeratorsWhicheverSideItWasWrittenOn() {
        Rational minusHalf = Rational.of(BigInteger.ONE, BigInteger.TWO.negate());
        assertEquals(Rational.of(BigInteger.ONE.negate(), BigInteger.TWO), minusHalf);
        assertEquals(BigInteger.ONE, minusHalf.denominator());
        assertEquals(-1, minusHalf.signum());
        assertEquals(half(), minusHalf.negated());
    }

    @Test
    void aQuotientOfWholeNumbersIsTheExactOne() {
        assertEquals(half(), Rational.of(1).dividedBy(Rational.of(2)));
        assertEquals(Rational.of(2), Rational.of(4).dividedBy(Rational.of(2)));
        assertEquals(Rational.of(-1).dividedBy(Rational.of(2)), half().negated());
        assertEquals(Rational.of(BigInteger.valueOf(7), BigInteger.valueOf(3)),
                Rational.of(7).dividedBy(Rational.of(3)));
    }

    /** Four halves is two, and the answer says so as a whole number rather than as a fraction that
     *  happens to reduce. */
    @Test
    void aQuotientThatIsWholeIsHeldAsOne() {
        Rational two = Rational.of(4).dividedBy(Rational.of(2));
        assertTrue(two.isWhole());
        assertEquals(BigInteger.TWO, two.asWholeNumber());
        assertEquals(new BigDecimal("2"), two.asDecimal());
        assertEquals(Rational.of(2), two);
    }

    @Test
    void theArithmeticIsTheNumberTheOperandsMake() {
        Rational third = Rational.of(BigInteger.ONE, BigInteger.valueOf(3));
        assertEquals(Rational.of(BigInteger.valueOf(5), BigInteger.valueOf(6)), half().plus(third));
        assertEquals(Rational.of(BigInteger.ONE, BigInteger.valueOf(6)), half().minus(third));
        assertEquals(Rational.of(BigInteger.ONE, BigInteger.valueOf(6)), half().times(third));
        assertEquals(Rational.of(BigInteger.valueOf(3), BigInteger.TWO), half().dividedBy(third));
        assertEquals(Rational.ZERO, half().minus(half()));
        assertEquals(Rational.of(3), third.times(Rational.of(9)));
    }

    /** A third has no finite decimal and says so, rather than answering the nearest one. */
    @Test
    void aValueWithNoDecimalAnswersNone() {
        Rational third = Rational.of(BigInteger.ONE, BigInteger.valueOf(3));
        assertNull(third.asDecimal());
        assertNull(third.asWholeNumber());
        assertEquals(new BigDecimal("0.5"), half().asDecimal());
        assertNull(half().asWholeNumber());
    }

    @Test
    void nothingIsDividedByNought() {
        assertThrows(IllegalArgumentException.class, Rational.ZERO::reciprocal);
        assertThrows(IllegalArgumentException.class, () -> Rational.of(1).dividedBy(Rational.ZERO));
    }

    @Test
    void theOrderIsByExactValue() {
        Rational third = Rational.of(BigInteger.ONE, BigInteger.valueOf(3));
        assertTrue(third.compareTo(half()) < 0);
        assertTrue(half().compareTo(third) > 0);
        assertEquals(0, half().compareTo(Rational.of(new BigDecimal("0.50"))));
        assertTrue(half().negated().compareTo(third) < 0);
        assertTrue(half().negated().compareTo(third.negated()) < 0);
        assertTrue(Rational.ZERO.compareTo(third.negated()) > 0);
    }

    /**
     * A part past what this representation stores has no value here and aborts, as an exponent past its
     * width does.
     *
     * <p>The bound is what makes the order total rather than something the order gives up on. Telling two
     * values apart takes as many bits as they agree over, and how closely two of these can stand is set by
     * their stored parts — so parts left to run to the platform's own end would want a bracket several times
     * that end, and a bracket is one whole number, whose bits the platform counts in an {@code int}. Then
     * the pair the order could not answer would be one no amount of room would answer, which is an
     * implementation's limit wearing the platform's name. A bound on the value instead is a bound the
     * language has a shape for, and this says out loud where it is.
     *
     * <p>Asserted on the numerator and on the denominator both. The value here is odd and no multiple of
     * five, so what is stored is what was written and the bound is reached by the value itself.
     */
    @Test
    void aPartPastWhatTheRepresentationStoresAborts() {
        BigInteger pastIt = BigInteger.ONE.shiftLeft(STORED_BITS + 1).subtract(BigInteger.valueOf(3));
        assertEquals(STORED_BITS + 1, pastIt.bitLength(), "one bit past the bound");
        assertTrue(pastIt.testBit(0) && pastIt.mod(BigInteger.valueOf(5)).signum() != 0,
                "and nothing about it comes off into an exponent");

        assertThrows(ConstraintViolation.class, () -> Rational.of(pastIt, BigInteger.ONE));
        assertThrows(ConstraintViolation.class, () -> Rational.of(BigInteger.ONE, pastIt));
        // and the value one bit narrower is held, which is the control for the bound being where it says
        assertEquals(STORED_BITS,
                Rational.of(pastIt.shiftRight(1).setBit(0), BigInteger.ONE).numerator().bitLength());
    }

    /**
     * And a part past the bound whose factors come off into the exponents is a value all the same.
     *
     * <p>The bound is on what is stored, and what a caller wrote is one spelling of the value. A numerator
     * of a hundred and thirty-four million bits that is a power of two is the number one here with the rest
     * of it in an exponent; one that is five times something is that something with a five in an exponent.
     * Read off the spelling, the bound turned away values this type holds — and turned them away for the
     * size of a form the implementation had picked, which is the one reason nothing here may refuse for.
     *
     * <p>Both halves matter and only together. Without the abort above, the bound says nothing; without
     * this, the bound is a bound on how a value may be written down.
     */
    @Test
    void aPartPastTheBoundWhoseFactorsComeOffIsStillAValue() {
        BigInteger fiveTimesSomething =
                BigInteger.ONE.shiftLeft(STORED_BITS + 1).subtract(BigInteger.ONE);
        assertEquals(STORED_BITS + 1, fiveTimesSomething.bitLength(), "one bit past the bound");
        assertEquals(0, fiveTimesSomething.mod(BigInteger.valueOf(5)).signum(), "and a multiple of five");

        Rational held = Rational.of(fiveTimesSomething, BigInteger.ONE);
        assertEquals(1L, held.fives(), "the five went to an exponent");
        assertTrue(held.numerator().bitLength() <= STORED_BITS, "and what is left is stored");

        // and the same of a power of two, which is the shape an exact Decimal arrives in (ADR-0116)
        Rational widened = Rational.of(new BigDecimal(BigInteger.ONE.shiftLeft(STORED_BITS + 1), 0));
        assertEquals(BigInteger.ONE, widened.numerator());
        assertEquals(STORED_BITS + 1L, widened.twos());
    }

    /**
     * The one rule {@link Values} needs of this type: its own equality and its own hash are the
     * language's, which is what the arm that asks a value for itself relies on.
     */
    @Test
    void theRuntimeAsksARationalForItsOwnEqualityAndHash() {
        assertTrue(Values.equal(half(), Rational.of(new BigDecimal("0.50"))));
        assertEquals(Values.hash(half()), Values.hash(Rational.of(new BigDecimal("0.50"))));
        assertNotEquals(half(), Rational.of(BigInteger.ONE, BigInteger.valueOf(3)));
    }
}
