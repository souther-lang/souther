package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import souther.runtime.Representations;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a decimal has at most so many digits, and the two answers built on it, agree with the
 * digit count itself at the edges: one digit either side of a power of ten, the numbers a bit length
 * alone settles, a thousand digits and one past, and scales across the whole of an int.
 */
class ADigitCountQuestionIsAnsweredWithoutCountingTheDigitsTest {

    private static final int[] SCALES = {Integer.MIN_VALUE, Integer.MIN_VALUE + 1, -1001, -1000, -999,
                                         -5, -1, 0, 1, 5, 998, 999, 1000, 1001, Integer.MAX_VALUE - 1,
                                         Integer.MAX_VALUE};

    @Test
    void hasAtMostDigitsIsTheDigitCountComparedWithTheLimit() {
        List<String> differ = new ArrayList<>();
        for (BigInteger unscaled : unscaledValues()) {
            BigDecimal d = new BigDecimal(unscaled);
            for (long limit : new long[] {0, 1, 2, 3, 4, 9, 10, 999, 1000, 1001}) {
                boolean expected = d.precision() <= limit;
                if (ExactDecimals.hasAtMostDigits(d, limit) != expected) {
                    differ.add(unscaled.bitLength() + " bits, limit " + limit);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void fitsPlainNotationIsTheLengthComparedWithTheLimit() {
        List<String> differ = new ArrayList<>();
        for (BigInteger unscaled : unscaledValues()) {
            for (int scale : SCALES) {
                BigDecimal d = new BigDecimal(unscaled, scale);
                boolean expected = ExactDecimals.plainNotationLength(d) <= ExactDecimals.MAX_SPELT_OUT_DIGITS;
                if (ExactDecimals.fitsPlainNotation(d) != expected) {
                    differ.add(unscaled.bitLength() + " bits at " + scale);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void leastDigitsIsOneFormPerAmount() {
        List<String> differ = new ArrayList<>();
        for (BigInteger unscaled : unscaledValues()) {
            for (int scale : SCALES) {
                BigDecimal d = new BigDecimal(unscaled, scale);
                BigDecimal least = ExactDecimals.leastDigits(d);
                boolean sameAmount = d.signum() == 0 || least.compareTo(d) == 0;
                if (!sameAmount || !sameForm(least, ExactDecimals.leastDigits(least))) {
                    differ.add(unscaled.bitLength() + " bits at " + scale);
                }
                if (scale > Integer.MIN_VALUE + 2000 && d.signum() != 0 && !sameForm(least, d.stripTrailingZeros())) {
                    differ.add("not stripped: " + unscaled.bitLength() + " bits at " + scale);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void leastDigitsStopsAtTheFloorWhateverNumberOfZerosItMeets() {
        List<String> differ = new ArrayList<>();
        for (int zeros : new int[] {0, 1, 2, 3, 4, 5, 9, 10, 11, 100, 511, 512, 513,
                              999, 1000, 1001, 1023, 1024, 1025}) {
            for (long odd : new long[] {1, 7, -7, 25, 3}) {
                BigInteger unscaled = BigInteger.TEN.pow(zeros).multiply(BigInteger.valueOf(odd));
                for (int offset : new int[] {0, 1, zeros - 1, zeros, zeros + 1, zeros + 2, 5000}) {
                    if (offset < 0) {
                        continue;
                    }
                    BigDecimal d = new BigDecimal(unscaled, Integer.MIN_VALUE + offset);
                    BigDecimal expected = oneZeroAtATime(unscaled, Integer.MIN_VALUE + offset);
                    BigDecimal asked = ExactDecimals.leastDigits(d);
                    if (!sameForm(asked, expected)) {
                        differ.add(odd + "e" + zeros + " at floor + " + offset);
                    }
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void aLimitPastWhatAnyDecimalHoldsIsMetByEvery() {
        BigDecimal wide = new BigDecimal(BigInteger.ONE.shiftLeft(100_000), Integer.MIN_VALUE);
        for (long limit : new long[] {Long.MAX_VALUE / 3 + 1, Long.MAX_VALUE / 4 + 1, Long.MAX_VALUE}) {
            assertTrue(ExactDecimals.hasAtMostDigits(BigDecimal.ONE, limit));
            assertTrue(ExactDecimals.hasAtMostDigits(wide, limit));
        }
        assertFalse(ExactDecimals.hasAtMostDigits(BigDecimal.ONE, 0));
        assertFalse(ExactDecimals.hasAtMostDigits(BigDecimal.ONE, Long.MIN_VALUE));
    }

    @Test
    void theCanonicalNumberSpellsOutExactlyWhereTheExpansionIsAThousandDigitsOrFewer() {
        List<String> differ = new ArrayList<>();
        for (BigInteger unscaled : unscaledValues()) {
            for (int scale : new int[] {-1, -2, -5, -990, -999, -1000, -1001, -1002, Integer.MIN_VALUE + 1}) {
                BigDecimal stripped = ExactDecimals.leastDigits(new BigDecimal(unscaled, scale));
                BigDecimal asked = Representations.canonicalNumber(new BigDecimal(unscaled, scale));
                boolean spelled = stripped.scale() < 0
                        && (long) stripped.precision() - stripped.scale() <= ExactDecimals.MAX_SPELT_OUT_DIGITS;
                BigDecimal expected = spelled ? stripped.setScale(0) : stripped;
                if (!sameForm(asked, expected)) {
                    differ.add(unscaled.bitLength() + " bits at " + scale);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void aProductAboveTheRangeGivesUpOnlyTheZerosItHas() {
        BigDecimal tenth = new BigDecimal(BigInteger.ONE, 1);
        BigDecimal hundredth = new BigDecimal(BigInteger.ONE, 2);
        BigDecimal one = new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE);
        BigDecimal ten = new BigDecimal(BigInteger.TEN, Integer.MAX_VALUE);
        BigDecimal hundred = new BigDecimal(BigInteger.TEN.pow(2), Integer.MAX_VALUE);
        BigDecimal thousandZeros = new BigDecimal(BigInteger.TEN.pow(1000), Integer.MAX_VALUE);
        assertTrue(sameForm(one, ExactDecimals.product(ten, tenth)));
        assertTrue(sameForm(new BigDecimal(BigInteger.TEN.pow(999), Integer.MAX_VALUE),
                ExactDecimals.product(thousandZeros, tenth)));
        assertTrue(sameForm(one, ExactDecimals.product(hundred, hundredth)));
        assertNull(ExactDecimals.product(one, tenth));
        assertNull(ExactDecimals.product(ten, hundredth));
    }

    /** The form a decimal is written in: the digits and the scale, which {@code compareTo} leaves out
     *  and {@code equals} is flagged for. */
    private static boolean sameForm(BigDecimal a, BigDecimal b) {
        return a.unscaledValue().equals(b.unscaledValue()) && a.scale() == b.scale();
    }

    private static BigDecimal oneZeroAtATime(BigInteger unscaled, int scale) {
        BigInteger digits = unscaled;
        int at = scale;
        while (at > Integer.MIN_VALUE) {
            BigInteger[] divided = digits.divideAndRemainder(BigInteger.TEN);
            if (divided[1].signum() != 0) {
                break;
            }
            digits = divided[0];
            at--;
        }
        return new BigDecimal(digits, at);
    }

    private static List<BigInteger> unscaledValues() {
        List<BigInteger> out = new ArrayList<>();
        for (int digits : new int[] {1, 2, 3, 4, 5, 18, 19, 20, 998, 999, 1000, 1001, 1002}) {
            BigInteger power = BigInteger.TEN.pow(digits - 1);
            for (BigInteger each : new BigInteger[] {
                    power, power.add(BigInteger.ONE), power.multiply(BigInteger.TEN).subtract(BigInteger.ONE),
                    power.multiply(BigInteger.TEN)}) {
                out.add(each);
                out.add(each.negate());
            }
        }
        for (int bits : new int[] {1, 2, 3, 4, 3000, 3001, 4000, 4001}) {
            BigInteger power = BigInteger.ONE.shiftLeft(bits);
            for (BigInteger each : new BigInteger[] {power, power.subtract(BigInteger.ONE)}) {
                out.add(each);
                out.add(each.negate());
            }
        }
        out.add(BigInteger.ZERO);
        out.add(BigInteger.ONE.shiftLeft(100_000).subtract(BigInteger.valueOf(3)));
        out.add(BigInteger.ONE.shiftLeft(100_000).subtract(BigInteger.valueOf(3)).negate());
        return out;
    }
}
