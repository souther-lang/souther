package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.exact.ExactDecimals;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link ExactRatio#spelled} answers for every value the type holds, in space that follows the
 * digits of its parts and not the size of its exponents.
 *
 * <p>An ordinary number keeps the spelling a report has always had. A decimal past the scale a
 * {@code BigDecimal} has is written the way one would be, so a number reads the same whichever type
 * carried it; and what is left of two or five once ten is taken out is named as a power rather than
 * written. {@link ExactRatio#toString} is the same answer, because it is reached without being asked.
 */
class ANumberIsNamedForAReaderWhateverItsScaleTest {

    private static final long FAR = 1L << 32;

    private static ExactRatio at(long numerator, long denominator, long twos, long fives) {
        return new ExactRatio(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator),
                twos, fives);
    }

    @Test
    void anOrdinaryDecimalIsSpelledAsItAlwaysWas() {
        assertEquals("0.5", ExactRatio.of(new BigDecimal("0.5")).spelled());
        assertEquals("123", ExactRatio.of(123).spelled());
        assertEquals("-0.25", ExactRatio.of(new BigDecimal("-0.250")).spelled());
    }

    @Test
    void anOrdinaryFractionIsSpelledAsItAlwaysWas() {
        assertEquals("1/3", ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3)).spelled());
        assertEquals("1/6", ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(6)).spelled());
        assertEquals("-7/12", ExactRatio.of(BigInteger.valueOf(-7), BigInteger.valueOf(12)).spelled());
    }

    /** Past a thousand digits but inside a {@code BigDecimal}'s scale: the decimal's own notation. */
    @Test
    void aDecimalPastAThousandDigitsIsTheDecimalsOwnExponentNotation() {
        BigDecimal fine = new BigDecimal(BigInteger.ONE, 1_000_000);

        assertEquals("1E-1000000", ExactRatio.of(fine).spelled());
        assertEquals(ExactDecimals.spelledBounded(fine), ExactRatio.of(fine).spelled());
    }

    /** Past the scale a {@code BigDecimal} has: the same notation, written here. */
    @Test
    void aDecimalPastEveryScaleIsWrittenTheWayADecimalWouldBe() {
        assertEquals("1E-4294967296", at(1, 1, -FAR, -FAR).spelled());
        assertEquals("7E+3000000000", at(7, 1, 3_000_000_000L, 3_000_000_000L).spelled());
        assertEquals("-3E-4294967296", at(-3, 1, -FAR, -FAR).spelled());
    }

    /** A power of two left over and small enough to write goes into the digits. */
    @Test
    void aSmallPowerLeftOverIsWrittenIntoTheDigits() {
        assertEquals("1.2E-4294967295", at(3, 1, 2 - FAR, -FAR).spelled());
    }

    @Test
    void aLargePowerLeftOverIsNamedRatherThanWritten() {
        assertEquals("7 * 2^123456789 * 10^-4294967296",
                at(7, 1, 123_456_789 - FAR, -FAR).spelled());
        assertEquals("1/3 * 10^-4294967296", at(1, 3, -FAR, -FAR).spelled());
    }

    /** The least exponent has no negation as a long, and the spelling never asks for one. */
    @Test
    void theLeastExponentIsSpelled() {
        assertEquals("1/3 * 10^-9223372036854775808",
                at(1, 3, Long.MIN_VALUE, Long.MIN_VALUE).spelled());
        assertEquals("1 * 5^9223372036854775808 * 10^-9223372036854775808",
                at(1, 1, Long.MIN_VALUE, 0).spelled());
        assertEquals("1 * 2^18446744073709551615 * 10^-9223372036854775808",
                at(1, 1, Long.MAX_VALUE, Long.MIN_VALUE).spelled());
    }

    /** Built two ways, one value, one spelling. */
    @Test
    void oneValueHasOneSpelling() {
        ExactRatio direct = at(1, 1, -FAR, -FAR);
        ExactRatio tenfold = new ExactRatio(BigInteger.TEN, BigInteger.ONE, -FAR - 1, -FAR - 1);

        assertEquals(direct, tenfold);
        assertEquals(direct.spelled(), tenfold.spelled());
    }

    @Test
    void theStringOfARatioIsItsSpelling() {
        ExactRatio far = at(7, 3, 123_456_789 - FAR, -FAR);

        assertEquals(far.spelled(), far.toString());
        assertEquals("0.5", ExactRatio.of(new BigDecimal("0.5")).toString());
    }
}
