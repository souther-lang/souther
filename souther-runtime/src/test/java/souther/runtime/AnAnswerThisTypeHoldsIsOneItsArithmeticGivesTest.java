package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a value and its answer are both ones this type holds, the arithmetic answers.
 *
 * <p>One rule, and the whole of what this class is about: an operation may abort because the answer
 * has no representation, and not because a step on the way to it has none. An exponent runs to
 * sixty-four bits, so a value at the end of that range is an ordinary value — and a middle step that
 * negated it, or multiplied it out, or counted it in a narrower number, refused a value the type holds
 * for a reason the caller cannot see and the answer does not have.
 *
 * <p>The four rows below are the shapes that reached for such a step. A quotient by way of a
 * reciprocal, a decimal by way of a non-negative scale, a rounding by way of the digits, and an order
 * by way of a count of bits: each was a step narrower than the value it was handed.
 */
class AnAnswerThisTypeHoldsIsOneItsArithmeticGivesTest {

    /** A value at the far end of the exponent's range, which squaring reaches. */
    private static Rational atTheEndOfTheRange() {
        Rational at = new Rational(BigInteger.ONE, BigInteger.ONE, Long.MIN_VALUE, 0);
        assertEquals(Long.MIN_VALUE, at.twos(), "the value this is about");
        return at;
    }

    /**
     * A value divided by itself is one, whatever its exponents are.
     *
     * <p>The quotient's exponents are the difference of the two, which is nought here. Reached through
     * the reciprocal, the difference is computed as a negation first — and the least sixty-four-bit
     * number has no positive counterpart, so a division that answers one refused to.
     */
    @Test
    void aValueDividedByItselfIsOne() {
        Rational at = atTheEndOfTheRange();

        assertEquals(Rational.ONE, at.dividedBy(at));
    }

    /**
     * And the decimal a decimal became comes back as that decimal.
     *
     * <p>The widening takes every scale, including the least one there is, whose negation is an
     * exponent no thirty-two-bit number holds. What it made is a value whose decimal is the one it came
     * from, so the narrowing back is a scale and not a power to build.
     */
    @Test
    void theDecimalADecimalBecameComesBackAsIt() {
        BigDecimal written = new BigDecimal(BigInteger.ONE, Integer.MIN_VALUE);

        BigDecimal back = Rational.of(written).asDecimal();

        assertEquals(0, written.compareTo(back), "the amount is the one that went in: " + back);
    }

    /**
     * And so does one whose most compact decimal is past the end a scale counts.
     *
     * <p>A decimal is written at any scale that clears both exponents, and the least of them is only the
     * most compact of the spellings. This decimal's own scale is the least there is, and its digits hold a
     * factor of ten — so widening it moves that ten into the exponents and the compact spelling of what
     * came back would need a scale one below the end. The decimal it came from is right there, one place
     * further up with the ten back in its digits, and that is the one to answer with.
     *
     * <p>Which is the same shape as the rest of this class, a step further in: the step was the canonical
     * spelling for the type on the way out, and a canonical spelling narrower than the type it is for
     * refuses values the type holds.
     */
    @Test
    void aDecimalWhoseCompactSpellingIsPastTheEndComesBackToo() {
        BigDecimal written = new BigDecimal(BigInteger.TEN, Integer.MIN_VALUE);
        Rational exact = Rational.of(written);
        assertEquals(2147483649L, exact.twos(), "the value this is about");

        BigDecimal back = (BigDecimal) RationalMath.toFiniteDecimal(exact);

        assertEquals(0, written.compareTo(back), "the amount is the one that went in: " + back);
    }

    /** And the other end is where a decimal really has none: a scale counts only so far up, and no
     *  spelling of a value needing more places reaches one. */
    @Test
    void aValueNeedingMorePlacesThanAScaleCountsHasNoDecimal() {
        Rational past = new Rational(BigInteger.ONE, BigInteger.ONE, -3_000_000_000L, -3_000_000_000L);

        assertTrue(past.hasFiniteDecimal(), "a denominator of one, so the decimal repeats nowhere");
        assertThrows(ConstraintViolation.class, () -> RationalMath.toFiniteDecimal(past));
    }

    /**
     * A value below half of what the asked scale counts rounds to nought, and says so.
     *
     * <p>What a rounding policy asks for is a value, which is the whole of what naming the policy
     * buys. Read through the digits, a value this small had a denominator of two to the two billionth
     * built for it, and the operation aborted where the answer was nought.
     */
    @Test
    void aValueBelowWhatAScaleCountsRoundsToNought() {
        Rational tiny = new Rational(BigInteger.ONE, BigInteger.ONE, Integer.MIN_VALUE, 0);

        assertEquals(0L, RationalMath.toInt(DOWN.INSTANCE, tiny));
        assertEquals(0L, RationalMath.toInt(HALF_UP.INSTANCE, tiny));
        assertEquals(0, BigDecimal.ZERO.compareTo(
                RationalMath.toDecimal(2, HALF_UP.INSTANCE, tiny)));
    }

    /** And the same value rounds away from nought where the policy says to. */
    @Test
    void aPolicyThatRoundsAwayFromNoughtStillDoes() {
        Rational tiny = new Rational(BigInteger.ONE, BigInteger.ONE, Integer.MIN_VALUE, 0);

        assertEquals(1L, RationalMath.toInt(UP.INSTANCE, tiny));
        assertEquals(1L, RationalMath.toInt(CEILING.INSTANCE, tiny));
        assertEquals(-1L, RationalMath.toInt(FLOOR.INSTANCE, tiny.negated()));
        assertEquals(0L, RationalMath.toInt(CEILING.INSTANCE, tiny.negated()),
                "and toward nought on the other side");
    }

    /**
     * A value standing just above one, made of two exponents that all but cancel, rounds.
     *
     * <p>The pair the order is hardest to answer for, written as one value: a power of two over the power
     * of five nearest below it, which stands a hair above one. Neither exponent is anywhere near nought,
     * so spelling the value out as digits asks for a number no machine holds — and the answer is one.
     *
     * <p>This is the shape a narrowing that rounded a decimal rather than the value refused. Standing
     * inside one place is not what makes such a value answerable, and treating that as the case to
     * rescue left every value above one place refused for the same reason it always was.
     */
    @Test
    void aValueJustAboveOneRoundsWithoutBuildingItsPowers() {
        Rational r = new Rational(BigInteger.ONE, BigInteger.ONE,
                3_086_630_039_907_612_845L, -1_329_339_201_633_350_533L);

        assertTrue(r.compareTo(Rational.ONE) > 0, "the value this is about stands above one");
        assertTrue(r.compareTo(Rational.of(2)) < 0);

        assertEquals(1L, RationalMath.toInt(DOWN.INSTANCE, r));
        assertEquals(1L, RationalMath.toInt(HALF_UP.INSTANCE, r));
        assertEquals(2L, RationalMath.toInt(UP.INSTANCE, r));
        assertEquals(-1L, RationalMath.toInt(DOWN.INSTANCE, r.negated()));
        assertEquals(0, BigDecimal.ONE.compareTo(
                RationalMath.toDecimal(0, DOWN.INSTANCE, r)));
        assertEquals(0, new BigDecimal("1.00").compareTo(
                RationalMath.toDecimal(2, DOWN.INSTANCE, r)),
                "and at a scale the value's own exponents are nowhere near");
    }

    /**
     * A value exactly half of what the scale counts goes to whichever neighbour the policy names.
     *
     * <p>The boundary between the two answers the rounding below one place can give, and the one where
     * it stands equal to what it is compared against rather than inside or outside it. Nought and one
     * place are the neighbours, and nought is the even one, so the policy that takes the even
     * neighbour and the one that takes the nearer nought agree here and only the two above them do not.
     */
    @Test
    void aValueAtHalfAPlaceGoesWhereThePolicySays() {
        Rational half = new Rational(BigInteger.ONE, BigInteger.ONE, -1, 0);

        assertEquals(1L, RationalMath.toInt(HALF_UP.INSTANCE, half));
        assertEquals(1L, RationalMath.toInt(UP.INSTANCE, half));
        assertEquals(0L, RationalMath.toInt(HALF_EVEN.INSTANCE, half));
        assertEquals(0L, RationalMath.toInt(HALF_DOWN.INSTANCE, half));
        assertEquals(0L, RationalMath.toInt(DOWN.INSTANCE, half));
        assertEquals(-1L, RationalMath.toInt(HALF_UP.INSTANCE, half.negated()));
    }

    /**
     * A very small value is below one, and the order says so.
     *
     * <p>Ordering is a capability this type states (spec §stdlib-rational), so it is answered over
     * every value the type holds. The bracket the answer usually comes from was counted in a number
     * narrower than the exponents it was reading, and what it could not bracket it handed to a step
     * that multiplied the exponents out.
     */
    @Test
    void aValueAtTheEndOfTheRangeIsStillOrdered() {
        Rational at = atTheEndOfTheRange();

        assertTrue(at.compareTo(Rational.ONE) < 0, "a halving repeated is below one");
        assertTrue(Rational.ONE.compareTo(at) > 0);
        assertTrue(at.compareTo(at.negated()) > 0);
        assertTrue(at.negated().compareTo(Rational.ONE) < 0);
    }

    /** And a value at the other end is above one. */
    @Test
    void aValueAtTheOtherEndIsAboveOne() {
        Rational far = new Rational(BigInteger.ONE, BigInteger.ONE, Long.MAX_VALUE, 0);

        assertTrue(far.compareTo(Rational.ONE) > 0);
        assertTrue(far.compareTo(new Rational(BigInteger.ONE, BigInteger.ONE, 0, Long.MAX_VALUE)) < 0,
                "a power of five outruns the same power of two");
    }
}
