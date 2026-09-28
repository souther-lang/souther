package souther.runtime;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A {@code Decimal} product's scale is the sum of its factors' scales, and a product whose sum is
 * outside the signed 32-bit scales aborts (spec §stdlib-decimal, §a-scale-is-used-as-the-number-written).
 *
 * <p>The factors are nought, one and minus one at scales from both ends of the range and around
 * nought, so the sums fall one past each end, on each end, and inside. Nought is on the left, on the
 * right and on both sides of a sum out of range in either direction: {@code BigDecimal} multiplies a
 * nought on its left at a scale moved back into range and refuses the same nought on its right, and
 * the rule does not depend on either.
 */
class AProductsScaleIsTheSumOfItsFactorsScalesTest {

    private static final List<BigInteger> DIGITS =
            List.of(BigInteger.ZERO, BigInteger.ONE, BigInteger.ONE.negate());

    private static final List<Integer> SCALES = List.of(
            Integer.MIN_VALUE, Integer.MIN_VALUE + 1, -1, 0, 1, Integer.MAX_VALUE - 1,
            Integer.MAX_VALUE);

    private record Pair(BigDecimal a, BigDecimal b) {

        boolean sumIsInRange() {
            long sum = sumOfScales(a, b);
            return sum == (int) sum;
        }

        Arguments arguments() {
            return Arguments.of(a, b);
        }
    }

    private static Stream<Pair> everyPair() {
        List<BigDecimal> factors = new ArrayList<>();
        for (BigInteger digits : DIGITS) {
            for (int scale : SCALES) {
                factors.add(new BigDecimal(digits, scale));
            }
        }
        List<Pair> pairs = new ArrayList<>();
        for (BigDecimal a : factors) {
            for (BigDecimal b : factors) {
                pairs.add(new Pair(a, b));
            }
        }
        return pairs.stream();
    }

    static Stream<Arguments> pairs() {
        return everyPair().map(Pair::arguments);
    }

    static Stream<Arguments> pairsWhoseSumIsInRange() {
        return everyPair().filter(Pair::sumIsInRange).map(Pair::arguments);
    }

    static Stream<Arguments> pairsWhoseSumIsOutOfRange() {
        return everyPair().filter(pair -> !pair.sumIsInRange()).map(Pair::arguments);
    }

    private static long sumOfScales(BigDecimal a, BigDecimal b) {
        return (long) a.scale() + b.scale();
    }

    @ParameterizedTest
    @MethodSource("pairsWhoseSumIsInRange")
    void aProductAtAScaleInRangeHasTheSumAsItsScale(BigDecimal a, BigDecimal b) {
        BigDecimal product = DecimalMath.multiply(a, b);
        assertEquals(sumOfScales(a, b), product.scale(), "the product's scale");
        assertEquals(a.unscaledValue().multiply(b.unscaledValue()), product.unscaledValue(),
                "the product's digits");
    }

    @ParameterizedTest
    @MethodSource("pairsWhoseSumIsOutOfRange")
    void aProductWhoseScaleIsOutOfRangeAbortsWhateverItsValue(BigDecimal a, BigDecimal b) {
        assertThrows(ConstraintViolation.class, () -> DecimalMath.multiply(a, b));
    }

    /** What the two rules above give, asked of the order the factors come in. */
    @ParameterizedTest
    @MethodSource("pairs")
    void theFactorsInEitherOrderGiveOneAnswer(BigDecimal a, BigDecimal b) {
        assertEquals(outcome(a, b), outcome(b, a));
    }

    private static String outcome(BigDecimal a, BigDecimal b) {
        try {
            BigDecimal product = DecimalMath.multiply(a, b);
            return product.unscaledValue() + " at scale " + product.scale();
        } catch (ConstraintViolation _) {
            return "aborted";
        }
    }
}
