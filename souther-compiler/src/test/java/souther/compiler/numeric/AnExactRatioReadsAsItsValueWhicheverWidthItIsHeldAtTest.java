package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.exact.ExactDecimals;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a ratio says of itself — its spelling, the decimal it is, whether it is a whole multiple of
 * another — is what its value says, whether its two whole numbers are held as longs or wider: worked
 * out here from the value's own fraction in {@code BigInteger}s and {@code BigDecimal}s, and asked of
 * values on both sides of what a long holds, of both signs, with exponents above and below nought.
 */
class AnExactRatioReadsAsItsValueWhicheverWidthItIsHeldAtTest {

    private record Value(ExactRatio ratio, BigInteger numerator, BigInteger denominator) {}

    private static List<Value> values() {
        List<BigInteger> wholes = new ArrayList<>();
        for (long each : new long[] {1, 3, 7, 21, 999_999_937L, (1L << 61) - 1, Long.MAX_VALUE}) {
            wholes.add(BigInteger.valueOf(each));
            wholes.add(BigInteger.valueOf(each).negate());
        }
        wholes.add(BigInteger.ONE.shiftLeft(70).add(BigInteger.valueOf(9)));
        List<BigInteger> denominators = List.of(BigInteger.ONE, BigInteger.valueOf(3),
                BigInteger.valueOf(7 * 9), BigInteger.ONE.shiftLeft(66).add(BigInteger.ONE));
        long[] exponents = {0, 1, -1, 4, -6, 20, -30};
        List<Value> out = new ArrayList<>();
        Random random = new Random(20261030L);
        for (BigInteger numerator : wholes) {
            for (BigInteger denominator : denominators) {
                long twos = exponents[random.nextInt(exponents.length)];
                long fives = exponents[random.nextInt(exponents.length)];
                ExactRatio ratio = new ExactRatio(numerator, denominator, twos, fives);
                BigInteger up = numerator.multiply(power(2, twos)).multiply(power(5, fives));
                BigInteger down = denominator.multiply(power(2, -twos)).multiply(power(5, -fives));
                BigInteger common = up.gcd(down);
                out.add(new Value(ratio, up.divide(common), down.divide(common)));
            }
        }
        return out;
    }

    private static BigInteger power(int base, long exponent) {
        return exponent > 0 ? BigInteger.valueOf(base).pow((int) exponent) : BigInteger.ONE;
    }

    /** The decimal a fraction is exactly, where its denominator divides a power of ten. */
    private static Optional<BigDecimal> decimalOf(Value value) {
        BigDecimal quotient = new BigDecimal(value.numerator());
        try {
            return Optional.of(quotient.divide(new BigDecimal(value.denominator()),
                    MathContext.UNLIMITED));
        } catch (ArithmeticException notADecimal) {
            return Optional.empty();
        }
    }

    @Test
    void aRatioIsSpelledAsItsValueIs() {
        List<String> differ = new ArrayList<>();
        for (Value each : values()) {
            Optional<BigDecimal> decimal = decimalOf(each);
            String expected = decimal.isPresent()
                    ? ExactDecimals.spelledBounded(ExactDecimals.leastDigits(decimal.get()))
                    : each.numerator() + "/" + each.denominator();
            if (!each.ratio().spelled().equals(expected)) {
                differ.add(each.ratio().key() + ": " + each.ratio().spelled() + " != " + expected);
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void aRatioIsTheDecimalItsValueIs() {
        List<String> differ = new ArrayList<>();
        for (Value each : values()) {
            Optional<BigDecimal> written = each.ratio().writtenDecimal().orFail("written");
            Optional<BigDecimal> expected = decimalOf(each);
            boolean same = written.isPresent() == expected.isPresent()
                    && (written.isEmpty() || written.get().compareTo(expected.get()) == 0);
            if (!same) {
                differ.add(each.ratio().key() + ": " + written + " != " + expected);
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void aRatioIsAWholeMultipleOfAnotherWhereTheirQuotientIsWhole() {
        List<String> differ = new ArrayList<>();
        List<Value> values = values();
        for (Value one : values) {
            for (Value other : values) {
                BigInteger up = one.numerator().multiply(other.denominator());
                BigInteger down = one.denominator().multiply(other.numerator());
                boolean expected = up.mod(down.abs()).signum() == 0;
                if (one.ratio().isWholeMultipleOf(other.ratio()) != expected) {
                    differ.add(one.ratio().key() + " over " + other.ratio().key() + ": " + !expected);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }
}
