package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A ratio is held in lowest terms, so two ways of writing one value are one value. What is built on
 * these compares canonical forms by their maps, and a map whose values are ratios only decides that
 * two forms are the same rule if equal ratios are equal here.
 */
class AnExactRatioIsOneValueHoweverItArrivedTest {

    private static ExactRatio ratio(long numerator, long denominator) {
        return ExactRatio.of(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator));
    }

    @Test
    void twoWritingsOfOneValueAreOneValue() {
        assertEquals(ratio(1, 3), ratio(2, 6));
        assertEquals(ratio(1, 3), ratio(-3, -9));
        assertEquals(ratio(1, 3).hashCode(), ratio(2, 6).hashCode());
    }

    @Test
    void aNegativeDenominatorMovesToTheNumerator() {
        assertEquals(BigInteger.valueOf(-1), ratio(1, -3).asFraction().numerator());
        assertEquals(BigInteger.valueOf(3), ratio(1, -3).asFraction().denominator());
    }

    @Test
    void zeroIsOneValueWhateverItWasOver() {
        assertEquals(ExactRatio.ZERO, ratio(0, 7));
        assertTrue(ratio(0, 7).isZero());
    }

    @Test
    void aZeroDenominatorIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> ratio(1, 0));
    }

    @Test
    void arithmeticIsExactWhereDecimalsWouldRound() {
        ExactRatio third = ratio(1, 3);
        assertEquals(ExactRatio.ONE, third.plus(third).orNull().plus(third).orNull(),
                "three thirds are one, which is what rounding a third at any scale loses");
        assertEquals(ratio(1, 9), third.times(third).orNull());
        assertEquals(ExactRatio.ONE, third.dividedBy(third).orNull());
        assertEquals(ratio(-1, 3), third.negated());
    }

    @Test
    void dividingByZeroIsACallersMistake() {
        assertThrows(ArithmeticException.class, () -> ExactRatio.ONE.dividedBy(ExactRatio.ZERO));
    }

    @Test
    void aWrittenDecimalArrivesExactly() {
        assertEquals(ratio(1, 2), ExactRatio.of(new BigDecimal("0.5")));
        assertEquals(ratio(1, 8), ExactRatio.of(new BigDecimal("0.125")));
        assertEquals(ExactRatio.of(300), ExactRatio.of(new BigDecimal("3E+2")),
                "a negative scale is a whole number written as a multiple of ten");
        assertEquals(ratio(-7, 100), ExactRatio.of(new BigDecimal("-0.07")));
    }

    @Test
    void aRatioThatTerminatesComesBackAsTheDecimalItIs() {
        assertEquals(new BigDecimal("0.5"), WrittenDecimals.of(ratio(1, 2)));
        assertEquals(new BigDecimal("0.125"), WrittenDecimals.of(ratio(1, 8)));
        assertEquals(new BigDecimal("0.12"), WrittenDecimals.of(ratio(3, 25)));
        assertEquals(new BigDecimal("7"), WrittenDecimals.of(ExactRatio.of(7)));
        assertEquals(new BigDecimal("-0.05"), WrittenDecimals.of(ratio(-1, 20)));
    }

    /** The whole reason this type exists: a third is not a decimal, and saying so is the answer
     *  rather than handing back a rounded one that a later reader cannot tell from an exact one. */
    @Test
    void aRatioThatDoesNotTerminateSaysSoRatherThanRounding() {
        assertNull(WrittenDecimals.of(ratio(1, 3)));
        assertNull(WrittenDecimals.of(ratio(2, 7)));
        assertNull(WrittenDecimals.of(ratio(1, 30)));
        assertNotNull(WrittenDecimals.of(ratio(1, 40)), "forty is twos and a five");
    }

    @Test
    void roundingIsTheCallersDirection() {
        assertEquals(new BigDecimal("0.34"), ratio(1, 3).asDecimal(RoundingMode.CEILING, 2).orNull());
        assertEquals(new BigDecimal("0.33"), ratio(1, 3).asDecimal(RoundingMode.FLOOR, 2).orNull());
    }

    @Test
    void wholeNumbersAreTakenOffEitherEnd() {
        assertEquals(BigInteger.ZERO, ratio(1, 3).floor().orNull());
        assertEquals(BigInteger.ONE, ratio(1, 3).ceiling().orNull());
        assertEquals(BigInteger.valueOf(-1), ratio(-1, 3).floor().orNull());
        assertEquals(BigInteger.ZERO, ratio(-1, 3).ceiling().orNull());
        assertEquals(BigInteger.TWO, ExactRatio.of(2).floor().orNull());
        assertEquals(BigInteger.TWO, ExactRatio.of(2).ceiling().orNull(),
                "a whole number is its own floor and its own ceiling");
        assertTrue(ExactRatio.of(2).isWhole());
    }

    /**
     * What generates the values a form's coefficients reach. A third and a half are both whole
     * multiples of a sixth: {@code gcd} of the numerators over {@code lcm} of the denominators.
     */
    @Test
    void theGreatestCommonDivisorIsTheLargestBothAreMultiplesOf() {
        assertEquals(ratio(1, 6), ExactRatio.gcd(ratio(1, 3), ratio(1, 2)));
        assertEquals(ExactRatio.of(3), ExactRatio.gcd(ExactRatio.of(3), ExactRatio.of(6)));
        assertEquals(ExactRatio.of(300), ExactRatio.gcd(ExactRatio.of(300), ExactRatio.of(600)),
                "which is what turns `300s + 600c <= 4800` into `s + 2c <= 16`");
        assertEquals(ExactRatio.ONE, ExactRatio.gcd(ExactRatio.of(2), ExactRatio.of(3)));
    }

    @Test
    void zeroDividesNothingSoItIsTheIdentityHere() {
        assertEquals(ExactRatio.of(3), ExactRatio.gcd(ExactRatio.ZERO, ExactRatio.of(3)));
        assertEquals(ExactRatio.of(3), ExactRatio.gcd(ExactRatio.of(3), ExactRatio.ZERO));
        assertEquals(ExactRatio.ZERO, ExactRatio.gcd(ExactRatio.ZERO, ExactRatio.ZERO));
    }

    @Test
    void aDivisorHasNoSign() {
        assertEquals(ExactRatio.of(3), ExactRatio.gcd(ExactRatio.of(-3), ExactRatio.of(6)));
        assertEquals(ExactRatio.of(3), ExactRatio.gcd(ExactRatio.of(-3), ExactRatio.of(-6)));
    }

    @Test
    void orderIsDecidedWithoutLeavingTheRatios() {
        assertTrue(ratio(1, 3).compareTo(ratio(1, 2)) < 0);
        assertTrue(ratio(1, 3).compareTo(ratio(2, 6)) == 0);
        assertTrue(ratio(-1, 3).compareTo(ratio(1, 3)) < 0);
        assertTrue(ExactRatio.of(10_000_000_000L).times(ExactRatio.of(10_000_000_000L)).orNull()
                .compareTo(ExactRatio.of(Long.MAX_VALUE)) > 0,
                "and past where a long stops, since comparing cross-multiplies");
    }

    /**
     * The fewest places a value stands above, over the whole range an {@code int} names and not
     * only where a bound doubled up to it would have looked. A count between where the doubling
     * gave up and the top of what an {@code int} holds is one this compiler still holds a decimal
     * at, and used to be answered with an uncaught exception instead of the count.
     */
    @Test
    void placesAValueStandsAboveIsFoundOverTheWholeIntRange() {
        assertEquals(4, held(new ExactRatio(BigInteger.ONE, BigInteger.ONE, -3, -3)));
        // Past where a bound doubled up from two would have given up before reaching this far.
        assertEquals(1_500_000_001,
                held(new ExactRatio(BigInteger.ONE, BigInteger.ONE, -1_500_000_000L, -1_500_000_000L)));
        // At the very top of what an int names, which a caller adding one to must not overflow.
        assertEquals(Integer.MAX_VALUE,
                held(new ExactRatio(BigInteger.ONE, BigInteger.ONE, -2_147_483_646L, -2_147_483_646L)));
        // Past what an int names at all: no count here answers, and not an exception.
        assertTrue(new ExactRatio(BigInteger.ONE, BigInteger.ONE, -2_147_483_747L, -2_147_483_747L)
                .placesItStandsAbove().isEmpty());
    }

    private static int held(ExactRatio at) {
        return at.placesItStandsAbove().getAsInt();
    }
}
