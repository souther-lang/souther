package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

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
