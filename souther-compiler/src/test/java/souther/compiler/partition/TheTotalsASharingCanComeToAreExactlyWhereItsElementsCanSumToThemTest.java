package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total is in the interval a sharing of elements can come to exactly where the least the
 * elements of every kind can sum to is no more than the total, and the greatest no less.
 *
 * <p>Asked of every whole total in a range, against lines drawn at random, so that a place where
 * one line of a kind passes another, a kind with nothing bounding it on one side, and a bound on
 * the total alone are each met.
 */
class TheTotalsASharingCanComeToAreExactlyWhereItsElementsCanSumToThemTest {

    private static final int[] SLOPES_OVER_TWO = {-4, -2, -1, 0, 1, 2, 4};

    private static ExactRatio ratio(long numerator, long denominator) {
        return ExactRatio.of(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator));
    }

    private static TotalsASharingCanComeTo.Line line(Random random) {
        return new TotalsASharingCanComeTo.Line(
                ratio(SLOPES_OVER_TWO[random.nextInt(SLOPES_OVER_TWO.length)], 2),
                ratio(random.nextInt(13) - 6, 1 + random.nextInt(2)));
    }

    private static List<TotalsASharingCanComeTo.Line> lines(Random random) {
        List<TotalsASharingCanComeTo.Line> out = new ArrayList<>();
        for (int each = random.nextInt(3); each > 0; each--) {
            out.add(line(random));
        }
        return out;
    }

    private static ExactRatio at(TotalsASharingCanComeTo.Line line, ExactRatio total) {
        return line.slope().times(total).flatMap(line.intercept()::plus).orNull();
    }

    /** The greatest of the lines at the total, or the least — null where there is no line. */
    private static ExactRatio extreme(List<TotalsASharingCanComeTo.Line> lines, ExactRatio total,
                                      boolean greatest) {
        ExactRatio out = null;
        for (TotalsASharingCanComeTo.Line each : lines) {
            ExactRatio here = at(each, total);
            if (out == null || (here.compareTo(out) > 0) == greatest) {
                out = here;
            }
        }
        return out;
    }

    /**
     * Whether elements of the kinds, so many of each, can be given numbers that come to the total,
     * worked out by giving them: each starts at the number nearest nought that its kind leaves it,
     * and the difference to the total is made up by moving them, one after another, as far as
     * their kinds leave them. Nothing is compared of what they sum to, so this is no reading of
     * the interval the code finds.
     */
    private static boolean canSumTo(List<TotalsASharingCanComeTo.Reach> reaches, int[] counts,
                                    ExactRatio total) {
        List<ExactRatio[]> bounds = new ArrayList<>();
        ExactRatio sum = ExactRatio.ZERO;
        List<ExactRatio> at = new ArrayList<>();
        for (int kind = 0; kind < reaches.size(); kind++) {
            TotalsASharingCanComeTo.Reach reach = reaches.get(kind);
            if ((reach.totalLow() != null && total.compareTo(reach.totalLow()) < 0)
                    || (reach.totalHigh() != null && total.compareTo(reach.totalHigh()) > 0)) {
                return false;
            }
            ExactRatio least = extreme(reach.lower(), total, true);
            ExactRatio most = extreme(reach.upper(), total, false);
            if (least != null && most != null && least.compareTo(most) > 0) {
                return false;
            }
            ExactRatio start = ExactRatio.ZERO;
            if (least != null && start.compareTo(least) < 0) {
                start = least;
            }
            if (most != null && start.compareTo(most) > 0) {
                start = most;
            }
            for (int each = 0; each < counts[kind]; each++) {
                bounds.add(new ExactRatio[] {least, most});
                at.add(start);
                sum = sum.plus(start).orNull();
            }
        }
        ExactRatio left = total.minus(sum).orNull();
        for (int each = 0; each < at.size() && left.signum() != 0; each++) {
            ExactRatio edge = bounds.get(each)[left.signum() > 0 ? 1 : 0];
            ExactRatio reach = edge == null ? left : edge.minus(at.get(each)).orNull();
            ExactRatio step = left.signum() > 0 ? (left.compareTo(reach) < 0 ? left : reach)
                    : (left.compareTo(reach) > 0 ? left : reach);
            left = left.minus(step).orNull();
        }
        return left.signum() == 0;
    }

    /**
     * A kind that leaves its element no number at a total is no kind at it, whatever the sums of
     * the others come to. One kind needs a number at least the total and a thousand and one and at
     * most nought, which it has only at a total of a thousand and one below nought or less; the
     * other has no least and a most of the total and a thousand and one, or nought.
     */
    @Test
    void aKindThatLeavesItsElementNoNumberAtATotalAllowsNoSharingThere() {
        TotalsASharingCanComeTo.Reach needsALotBelowNought = new TotalsASharingCanComeTo.Reach(
                List.of(new TotalsASharingCanComeTo.Line(ExactRatio.ONE, ratio(1001, 1))),
                List.of(new TotalsASharingCanComeTo.Line(ExactRatio.ZERO, ExactRatio.ZERO)),
                null, null);
        TotalsASharingCanComeTo.Reach noLeast = new TotalsASharingCanComeTo.Reach(List.of(),
                List.of(new TotalsASharingCanComeTo.Line(ExactRatio.ONE, ratio(1001, 1)),
                        new TotalsASharingCanComeTo.Line(ExactRatio.ZERO, ExactRatio.ZERO)),
                null, null);
        TotalsASharingCanComeTo.Interval found = TotalsASharingCanComeTo.of(
                List.of(needsALotBelowNought, noLeast), new int[] {1, 1}, new HashSet<>());
        assertEquals(null, found.low());
        assertEquals(ratio(-1001, 1), found.high());
    }

    @Test
    void aTotalIsInTheIntervalWhereTheElementsCanSumToIt() {
        Random random = new Random(20261024);
        int nonEmpty = 0;
        int unbounded = 0;
        for (int round = 0; round < 1500; round++) {
            List<TotalsASharingCanComeTo.Reach> reaches = new ArrayList<>();
            int[] counts = new int[1 + random.nextInt(3)];
            for (int kind = 0; kind < counts.length; kind++) {
                counts[kind] = 1 + random.nextInt(4);
                reaches.add(new TotalsASharingCanComeTo.Reach(lines(random), lines(random),
                        random.nextInt(4) == 0 ? ratio(random.nextInt(21) - 10, 1) : null,
                        random.nextInt(4) == 0 ? ratio(random.nextInt(21) - 10, 1) : null));
            }
            TotalsASharingCanComeTo.Interval found =
                    TotalsASharingCanComeTo.of(reaches, counts, new HashSet<>());
            String drawn = reaches + " of " + Arrays.toString(counts) + " came to " + found;
            for (int total = -30; total <= 30; total++) {
                ExactRatio at = ExactRatio.of(total);
                boolean in = found != null
                        && (found.low() == null || found.low().compareTo(at) <= 0)
                        && (found.high() == null || found.high().compareTo(at) >= 0);
                assertEquals(canSumTo(reaches, counts, at), in, "at " + at + " in " + drawn);
            }
            nonEmpty += found == null ? 0 : 1;
            unbounded += found != null && (found.low() == null || found.high() == null) ? 1 : 0;
        }
        // The draws reach intervals, none, and ones that run on without end.
        assertTrue(nonEmpty > 150, "intervals met: " + nonEmpty);
        assertTrue(unbounded > 40, "unbounded intervals met: " + unbounded);
    }
}
