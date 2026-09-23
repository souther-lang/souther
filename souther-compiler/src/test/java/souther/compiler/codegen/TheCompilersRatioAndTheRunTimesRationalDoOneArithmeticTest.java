package souther.compiler.codegen;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import souther.compiler.numeric.ExactRatio;
import souther.runtime.ConstraintViolation;
import souther.runtime.OutOfRoom;
import souther.runtime.Rational;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The compiler's exact ratio and the run time's rational are two types that answer alike.
 *
 * <p>What a program computes and what the compiler proves about it are one mathematics, and the two
 * types carry it by one implementation ({@code souther.exact}). What is left for each type to get wrong
 * is its own layer: the parts it hands the arithmetic, the value it makes of an answer, and how it says a
 * failure. So every pair over values at both ends of the exponent's range is asked of both, and each
 * operation must give the same value from both or fail in both — in the terms each type uses, an
 * {@link ArithmeticException} for the ratio and an abort of the language for the rational.
 *
 * <p>Here and not beside either type because this is the one place that may name both: the compiler's
 * reasoning is kept from naming the run time's package, and the run time knows nothing of the compiler.
 */
class TheCompilersRatioAndTheRunTimesRationalDoOneArithmeticTest {

    private static final long[] TWOS = {Long.MIN_VALUE, -(1L << 40), -3, 0, 5, Long.MAX_VALUE};

    private static final long[] FIVES = {Long.MIN_VALUE, -(1L << 33), -2, 0, 4, Long.MAX_VALUE};

    private static final RoundingMode[] POLICIES = {
            RoundingMode.UP, RoundingMode.DOWN, RoundingMode.CEILING, RoundingMode.FLOOR,
            RoundingMode.HALF_UP, RoundingMode.HALF_DOWN, RoundingMode.HALF_EVEN};

    private record Pair(ExactRatio ratio, Rational rational) {
        @Override
        public String toString() {
            return ratio.key();
        }
    }

    /** What an operation came to: four parts, or that it failed. */
    private record Came(List<Object> parts) {
        static Came failed() {
            return new Came(List.of());
        }
    }

    private static List<Pair> values() {
        List<Pair> out = new ArrayList<>();
        for (long n : new long[] {1, -3, 7}) {
            for (long d : new long[] {1, 3}) {
                for (long twos : TWOS) {
                    for (long fives : FIVES) {
                        BigInteger numerator = BigInteger.valueOf(n);
                        BigInteger denominator = BigInteger.valueOf(d);
                        out.add(new Pair(new ExactRatio(numerator, denominator, twos, fives),
                                new Rational(numerator, denominator, twos, fives)));
                    }
                }
            }
        }
        return out;
    }

    private static Came ofRatio(Supplier<ExactRatio> operation) {
        try {
            ExactRatio r = operation.get();
            return new Came(List.of(r.numeratorWithoutUnits(), r.denominatorWithoutUnits(),
                    r.twos(), r.fives()));
        } catch (ArithmeticException _) {
            return Came.failed();
        }
    }

    private static Came ofRational(Supplier<Rational> operation) {
        try {
            Rational r = operation.get();
            return new Came(List.of(r.numerator(), r.denominator(), r.twos(), r.fives()));
        } catch (ConstraintViolation | OutOfRoom _) {
            return Came.failed();
        }
    }

    @Test
    @Timeout(120)
    void everyOperationGivesTheSameValueFromBothOrFailsInBoth() {
        List<Pair> values = values();
        int answered = 0;
        int failed = 0;
        for (Pair a : values) {
            for (Pair b : values) {
                Came plus = ofRatio(() -> a.ratio().plus(b.ratio()));
                assertEquals(plus, ofRational(() -> a.rational().plus(b.rational())), a + " + " + b);
                Came times = ofRatio(() -> a.ratio().times(b.ratio()));
                assertEquals(times, ofRational(() -> a.rational().times(b.rational())), a + " * " + b);
                Came over = ofRatio(() -> a.ratio().dividedBy(b.ratio()));
                assertEquals(over, ofRational(() -> a.rational().dividedBy(b.rational())), a + " / " + b);
                assertEquals(Integer.signum(a.ratio().compareTo(b.ratio())),
                        Integer.signum(a.rational().compareTo(b.rational())), a + " against " + b);
                for (Came each : List.of(plus, times, over)) {
                    if (each.parts().isEmpty()) {
                        failed++;
                    } else {
                        answered++;
                    }
                }
            }
        }
        assertTrue(answered > 1000, "the operations are answered in a population and not a handful: " + answered);
        assertTrue(failed > 1000, "and refused in one, both ends of the range being asked: " + failed);
    }

    @Test
    @Timeout(120)
    void everyRoundingGivesTheSameNumberFromBothOrFailsInBoth() {
        int rounded = 0;
        for (Pair each : values()) {
            for (RoundingMode towards : POLICIES) {
                for (int scale : new int[] {-2, 0, 3}) {
                    BigDecimal fromRatio = decimalOf(() -> each.ratio().asDecimal(towards, scale));
                    BigDecimal fromRational = decimalOf(
                            () -> each.rational().asDecimal(scale, towards));
                    assertEquals(fromRatio, fromRational, each + " at " + scale + " " + towards);
                    if (fromRatio != null) {
                        rounded++;
                    }
                }
            }
        }
        assertTrue(rounded > 1000, "some are answered, or the roundings agree over nothing: " + rounded);
    }

    /** The decimal an operation gave, or null where it was refused in either type's terms. */
    private static BigDecimal decimalOf(Supplier<BigDecimal> operation) {
        try {
            return operation.get();
        } catch (ArithmeticException | ConstraintViolation | OutOfRoom _) {
            return null;
        }
    }
}
