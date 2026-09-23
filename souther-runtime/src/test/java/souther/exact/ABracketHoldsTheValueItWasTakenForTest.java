package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every bracket the order is read from holds the value it was taken for.
 *
 * <p>The order itself is a poor place to ask this. A bracket that had slipped a bit off the value still
 * answers nearly every pair the way a sound one does — two magnitudes that differ at all usually differ by
 * far more than a working width's last bit — so a fault here passes hundreds of thousands of pairs and
 * waits for the one that matters. What makes the order right is the invariant and not the answers, and the
 * invariant is what this asks about.
 *
 * <p>Asked at widths far below the one a reading starts at, because a wide bracket is a tight one and a
 * tight bracket hides exactly the rounding this is about.
 */
class ABracketHoldsTheValueItWasTakenForTest {

    private static final BigInteger FIVE = BigInteger.valueOf(5);

    /** From the narrowest a reading is taken at, upward. Below it the two ends of a bracket spread
     *  through a product until the lower one falls to nought, which {@code reciprocal} refuses. */
    private static final int[] WIDTHS = {ExactOrder.BRACKET_BITS, 192, 256, 512};

    private static ExactParts parts(BigInteger numerator, BigInteger denominator, long twos, long fives) {
        return ExactArithmetic.canonical(numerator, denominator, twos, fives);
    }

    /** The numerator of {@code |of|} written out over the denominator below. */
    private static BigInteger up(ExactParts of) {
        return of.numerator().abs().multiply(power(of.twos(), BigInteger.TWO))
                .multiply(power(of.fives(), FIVE));
    }

    private static BigInteger down(ExactParts of) {
        return of.denominator().multiply(power(-of.twos(), BigInteger.TWO))
                .multiply(power(-of.fives(), FIVE));
    }

    private static BigInteger power(long exponent, BigInteger of) {
        return exponent <= 0 ? BigInteger.ONE : of.pow((int) exponent);
    }

    /**
     * That {@code low × 2^shift ≤ |of| ≤ high × 2^shift}, worked out over one denominator in whole
     * numbers — which is what the mechanism may not do and a test of it may.
     */
    private static void holds(ExactParts of, int width) {
        ExactOrder.Bracketed bracket = ExactOrder.bracketedMagnitude(of, width);
        BigInteger shift = bracket.shift();
        assertTrue(atLeast(up(of), down(of), bracket.low(), shift),
                () -> "the low end of a bracket of " + width + " bits is over " + of);
        assertTrue(noMoreThan(up(of), down(of), bracket.high(), shift),
                () -> "the high end of a bracket of " + width + " bits is under " + of);
    }

    /** Whether {@code end × 2^shift ≤ n/d}. */
    private static boolean atLeast(BigInteger n, BigInteger d, BigInteger end, BigInteger shift) {
        int by = shift.intValueExact();
        BigInteger scaled = by >= 0 ? end.multiply(d).shiftLeft(by) : end.multiply(d);
        BigInteger against = by >= 0 ? n : n.shiftLeft(-by);
        return scaled.compareTo(against) <= 0;
    }

    /** Whether {@code n/d ≤ end × 2^shift}. */
    private static boolean noMoreThan(BigInteger n, BigInteger d, BigInteger end, BigInteger shift) {
        int by = shift.intValueExact();
        BigInteger scaled = by >= 0 ? end.multiply(d).shiftLeft(by) : end.multiply(d);
        BigInteger against = by >= 0 ? n : n.shiftLeft(-by);
        return against.compareTo(scaled) <= 0;
    }

    private static List<ExactParts> values() {
        List<ExactParts> out = new ArrayList<>();
        out.add(parts(BigInteger.ONE, BigInteger.ONE, 0, 0));
        out.add(parts(BigInteger.ONE, BigInteger.valueOf(3), 0, 0));
        out.add(parts(BigInteger.valueOf(3), BigInteger.valueOf(7), 0, 0));
        out.add(parts(BigInteger.ONE, BigInteger.ONE, -1, -1));
        out.add(parts(BigInteger.valueOf(12345678), BigInteger.ONE, -4, -4));
        out.add(parts(BigInteger.valueOf(-12345678), BigInteger.ONE, -4, -4));
        Random pick = new Random(1799L);
        for (int i = 0; i < 2000; i++) {
            out.add(parts(
                    BigInteger.valueOf(pick.nextInt(1 << 20) - (1 << 19)).max(BigInteger.ONE),
                    BigInteger.valueOf(pick.nextInt(1 << 20) + 1),
                    pick.nextInt(121) - 60,
                    pick.nextInt(121) - 60));
        }
        return out;
    }

    @Test
    void everyBracketHoldsItsValueAtEveryWidth() {
        for (ExactParts each : values()) {
            for (int width : WIDTHS) {
                holds(each, width);
            }
        }
    }

    /**
     * Cutting a bracket back to a width never lets go of what it held.
     *
     * <p>The step the whole mechanism rests on, and the one no answer it gives would report: the two ends
     * move by a bit, and a bracket a bit too tight still answers every pair the sound one does until the
     * day it does not. So it is asked here directly, and at widths narrow enough that which way each end
     * was rounded shows.
     */
    @Test
    void cuttingABracketBackNeverLetsGoOfWhatItHeld() {
        Random pick = new Random(1800L);
        for (int i = 0; i < 20_000; i++) {
            BigInteger low = new BigInteger(1 + pick.nextInt(200), pick).add(BigInteger.ONE);
            BigInteger high = low.add(new BigInteger(1 + pick.nextInt(200), pick));
            BigInteger shift = BigInteger.valueOf(pick.nextInt(41) - 20);
            int width = 1 + pick.nextInt(24);
            ExactOrder.Bracketed cut = new ExactOrder.Bracketed(low, high, shift).keptTo(width);
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
        for (ExactParts each : values()) {
            for (int width : WIDTHS) {
                ExactOrder.Bracketed bracket = ExactOrder.bracketedMagnitude(each, width);
                assertTrue(bracket.low().compareTo(bracket.high()) <= 0,
                        () -> "the ends of a bracket of " + width + " bits are the wrong way round"
                                + " for " + each);
                assertTrue(bracket.low().signum() > 0,
                        () -> "a magnitude stands above nought, and so do the ends that hold it");
            }
        }
    }
}
