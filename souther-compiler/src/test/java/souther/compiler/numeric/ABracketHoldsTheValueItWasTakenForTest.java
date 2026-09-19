package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every bracket the order is read from holds the value it was taken for.
 *
 * <p>The order itself is a poor place to ask this. A bracket that had slipped a bit off the value
 * still answers nearly every pair the way a sound one does — two magnitudes that differ at all
 * usually differ by far more than a working width's last bit — so a fault here passes hundreds of
 * thousands of pairs and waits for the one that matters. What makes the order right is the invariant
 * and not the answers, and the invariant is what this asks about.
 *
 * <p>Asked at widths far below the one a reading starts at, because a wide bracket is a tight one
 * and a tight bracket hides exactly the rounding this is about.
 */
class ABracketHoldsTheValueItWasTakenForTest {

    /** From the narrowest a reading is taken at, upward. Below it the two ends of a bracket spread
     *  through a product until the lower one falls to nought, which {@code reciprocal} refuses. */
    private static final int[] WIDTHS =
            {ExactRatioOrder.FIRST_WIDTH, 192, 256, 512};

    /**
     * That {@code low × 2^shift ≤ |of| ≤ high × 2^shift}, worked out over one denominator in whole
     * numbers — which is what the mechanism may not do and a test of it may.
     */
    private static void holds(ExactRatio of, int width) {
        ExactRatioOrder.Bracketed bracket = ExactRatioOrder.magnitude(of, width);
        BigInteger shift = bracket.shift();
        ExactRatio.Fraction size = of.abs().asFraction();
        // |of| = n/d, and an end stands at e × 2^s. Over the denominator both are whole: n against
        // e × d × 2^s where the shift is upward, and n × 2^-s against e × d where it is downward.
        assertTrue(atLeast(size, bracket.low(), shift),
                () -> "the low end of a bracket of " + width + " bits is over " + of);
        assertTrue(noMoreThan(size, bracket.high(), shift),
                () -> "the high end of a bracket of " + width + " bits is under " + of);
    }

    /** Whether {@code end × 2^shift ≤ n/d}. */
    private static boolean atLeast(ExactRatio.Fraction size, BigInteger end, BigInteger shift) {
        int by = shift.intValueExact();
        BigInteger scaled = by >= 0 ? end.multiply(size.denominator()).shiftLeft(by)
                : end.multiply(size.denominator());
        BigInteger against = by >= 0 ? size.numerator() : size.numerator().shiftLeft(-by);
        return scaled.compareTo(against) <= 0;
    }

    /** Whether {@code n/d ≤ end × 2^shift}. */
    private static boolean noMoreThan(ExactRatio.Fraction size, BigInteger end, BigInteger shift) {
        int by = shift.intValueExact();
        BigInteger scaled = by >= 0 ? end.multiply(size.denominator()).shiftLeft(by)
                : end.multiply(size.denominator());
        BigInteger against = by >= 0 ? size.numerator() : size.numerator().shiftLeft(-by);
        return against.compareTo(scaled) <= 0;
    }

    private static List<ExactRatio> values() {
        List<ExactRatio> out = new ArrayList<>();
        out.add(ExactRatio.ONE);
        out.add(ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3)));
        out.add(ExactRatio.of(BigInteger.valueOf(3), BigInteger.valueOf(7)));
        out.add(ExactRatio.of(new java.math.BigDecimal("0.1")));
        out.add(ExactRatio.of(new java.math.BigDecimal("1234.5678")));
        out.add(ExactRatio.of(new java.math.BigDecimal("-1234.5678")));
        Random pick = new Random(1799L);
        for (int i = 0; i < 2000; i++) {
            out.add(new ExactRatio(
                    BigInteger.valueOf(pick.nextInt(1 << 20) - (1 << 19)).max(BigInteger.ONE),
                    BigInteger.valueOf(pick.nextInt(1 << 20) + 1),
                    pick.nextInt(121) - 60,
                    pick.nextInt(121) - 60));
        }
        return out;
    }

    @Test
    void everyBracketHoldsItsValueAtEveryWidth() {
        for (ExactRatio each : values()) {
            if (each.isZero()) {
                continue;
            }
            for (int width : WIDTHS) {
                holds(each, width);
            }
        }
    }

    /**
     * Cutting a bracket back to a width never lets go of what it held.
     *
     * <p>The step the whole mechanism rests on, and the one no answer it gives would report: the two
     * ends move by a bit, and a bracket a bit too tight still answers every pair the sound one does
     * until the day it does not. So it is asked here directly, and at widths narrow enough that
     * which way each end was rounded shows.
     */
    @Test
    void cuttingABracketBackNeverLetsGoOfWhatItHeld() {
        Random pick = new Random(1800L);
        for (int i = 0; i < 20_000; i++) {
            BigInteger low = new BigInteger(1 + pick.nextInt(200), pick).add(BigInteger.ONE);
            BigInteger high = low.add(new BigInteger(1 + pick.nextInt(200), pick));
            BigInteger shift = BigInteger.valueOf(pick.nextInt(41) - 20);
            int width = 1 + pick.nextInt(24);
            ExactRatioOrder.Bracketed cut =
                    new ExactRatioOrder.Bracketed(low, high, shift).keptTo(width);
            assertTrue(noGreater(cut.low(), cut.shift(), low, shift),
                    () -> "the low end rose above " + low + " at a width of " + width);
            assertTrue(noGreater(high, shift, cut.high(), cut.shift()),
                    () -> "the high end fell below " + high + " at a width of " + width);
        }
    }

    /** Whether {@code a × 2^sa ≤ b × 2^sb}, both whole numbers standing above nought. */
    private static boolean noGreater(BigInteger a, BigInteger sa, BigInteger b, BigInteger sb) {
        int shared = sa.min(sb).intValueExact();
        return a.shiftLeft(sa.intValueExact() - shared)
                .compareTo(b.shiftLeft(sb.intValueExact() - shared)) <= 0;
    }

    /** And the ends are the way round they are named, which is what the two readings above rest on
     *  telling apart. */
    @Test
    void theLowEndIsNoHigherThanTheHigh() {
        for (ExactRatio each : values()) {
            if (each.isZero()) {
                continue;
            }
            for (int width : WIDTHS) {
                ExactRatioOrder.Bracketed bracket = ExactRatioOrder.magnitude(each, width);
                assertTrue(bracket.low().compareTo(bracket.high()) <= 0,
                        () -> "the ends of a bracket of " + width + " bits are the wrong way round"
                                + " for " + each);
                assertTrue(bracket.low().signum() > 0,
                        () -> "a magnitude stands above nought, and so do the ends that hold it");
            }
        }
    }
}
