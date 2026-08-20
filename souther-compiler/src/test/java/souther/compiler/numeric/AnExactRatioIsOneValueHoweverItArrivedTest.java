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

    private static Rational ratio(long numerator, long denominator) {
        return Rational.of(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator));
    }

    @Test
    void twoWritingsOfOneValueAreOneValue() {
        assertEquals(ratio(1, 3), ratio(2, 6));
        assertEquals(ratio(1, 3), ratio(-3, -9));
        assertEquals(ratio(1, 3).hashCode(), ratio(2, 6).hashCode());
    }

    @Test
    void aNegativeDenominatorMovesToTheNumerator() {
        assertEquals(BigInteger.valueOf(-1), ratio(1, -3).numerator());
        assertEquals(BigInteger.valueOf(3), ratio(1, -3).denominator());
    }

    @Test
    void zeroIsOneValueWhateverItWasOver() {
        assertEquals(Rational.ZERO, ratio(0, 7));
        assertTrue(ratio(0, 7).isZero());
    }

    @Test
    void aZeroDenominatorIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> ratio(1, 0));
    }

    @Test
    void arithmeticIsExactWhereDecimalsWouldRound() {
        Rational third = ratio(1, 3);
        assertEquals(Rational.ONE, third.plus(third).plus(third),
                "three thirds are one, which is what rounding a third at any scale loses");
        assertEquals(ratio(1, 9), third.times(third));
        assertEquals(Rational.ONE, third.dividedBy(third));
        assertEquals(ratio(-1, 3), third.negated());
    }

    @Test
    void dividingByZeroIsACallersMistake() {
        assertThrows(ArithmeticException.class, () -> Rational.ONE.dividedBy(Rational.ZERO));
    }

    @Test
    void aWrittenDecimalArrivesExactly() {
        assertEquals(ratio(1, 2), Rational.of(new BigDecimal("0.5")));
        assertEquals(ratio(1, 8), Rational.of(new BigDecimal("0.125")));
        assertEquals(Rational.of(300), Rational.of(new BigDecimal("3E+2")),
                "a negative scale is a whole number written as a multiple of ten");
        assertEquals(ratio(-7, 100), Rational.of(new BigDecimal("-0.07")));
    }

    @Test
    void aRatioThatTerminatesComesBackAsTheDecimalItIs() {
        assertEquals(new BigDecimal("0.5"), ratio(1, 2).asWrittenDecimal());
        assertEquals(new BigDecimal("0.125"), ratio(1, 8).asWrittenDecimal());
        assertEquals(new BigDecimal("0.12"), ratio(3, 25).asWrittenDecimal());
        assertEquals(new BigDecimal("7"), Rational.of(7).asWrittenDecimal());
        assertEquals(new BigDecimal("-0.05"), ratio(-1, 20).asWrittenDecimal());
    }

    /** The whole reason this type exists: a third is not a decimal, and saying so is the answer
     *  rather than handing back a rounded one that a later reader cannot tell from an exact one. */
    @Test
    void aRatioThatDoesNotTerminateSaysSoRatherThanRounding() {
        assertNull(ratio(1, 3).asWrittenDecimal());
        assertNull(ratio(2, 7).asWrittenDecimal());
        assertNull(ratio(1, 30).asWrittenDecimal());
        assertNotNull(ratio(1, 40).asWrittenDecimal(), "forty is twos and a five");
    }

    @Test
    void roundingIsTheCallersDirection() {
        assertEquals(new BigDecimal("0.34"), ratio(1, 3).asDecimal(RoundingMode.CEILING, 2));
        assertEquals(new BigDecimal("0.33"), ratio(1, 3).asDecimal(RoundingMode.FLOOR, 2));
    }

    @Test
    void wholeNumbersAreTakenOffEitherEnd() {
        assertEquals(BigInteger.ZERO, ratio(1, 3).floor());
        assertEquals(BigInteger.ONE, ratio(1, 3).ceiling());
        assertEquals(BigInteger.valueOf(-1), ratio(-1, 3).floor());
        assertEquals(BigInteger.ZERO, ratio(-1, 3).ceiling());
        assertEquals(BigInteger.TWO, Rational.of(2).floor());
        assertEquals(BigInteger.TWO, Rational.of(2).ceiling(),
                "a whole number is its own floor and its own ceiling");
        assertTrue(Rational.of(2).isWhole());
    }

    /**
     * What generates the values a form's coefficients reach. A third and a half are both whole
     * multiples of a sixth: {@code gcd} of the numerators over {@code lcm} of the denominators.
     */
    @Test
    void theGreatestCommonDivisorIsTheLargestBothAreMultiplesOf() {
        assertEquals(ratio(1, 6), Rational.gcd(ratio(1, 3), ratio(1, 2)));
        assertEquals(Rational.of(3), Rational.gcd(Rational.of(3), Rational.of(6)));
        assertEquals(Rational.of(300), Rational.gcd(Rational.of(300), Rational.of(600)),
                "which is what turns `300s + 600c <= 4800` into `s + 2c <= 16`");
        assertEquals(Rational.ONE, Rational.gcd(Rational.of(2), Rational.of(3)));
    }

    @Test
    void zeroDividesNothingSoItIsTheIdentityHere() {
        assertEquals(Rational.of(3), Rational.gcd(Rational.ZERO, Rational.of(3)));
        assertEquals(Rational.of(3), Rational.gcd(Rational.of(3), Rational.ZERO));
        assertEquals(Rational.ZERO, Rational.gcd(Rational.ZERO, Rational.ZERO));
    }

    @Test
    void aDivisorHasNoSign() {
        assertEquals(Rational.of(3), Rational.gcd(Rational.of(-3), Rational.of(6)));
        assertEquals(Rational.of(3), Rational.gcd(Rational.of(-3), Rational.of(-6)));
    }

    @Test
    void orderIsDecidedWithoutLeavingTheRatios() {
        assertTrue(ratio(1, 3).compareTo(ratio(1, 2)) < 0);
        assertTrue(ratio(1, 3).compareTo(ratio(2, 6)) == 0);
        assertTrue(ratio(-1, 3).compareTo(ratio(1, 3)) < 0);
        assertTrue(Rational.of(10_000_000_000L).times(Rational.of(10_000_000_000L))
                .compareTo(Rational.of(Long.MAX_VALUE)) > 0,
                "and past where a long stops, since comparing cross-multiplies");
    }
}
