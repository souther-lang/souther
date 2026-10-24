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

    /** The sum, over the elements, of the greatest or least of the lines at the total — or null
     *  where a kind has no line to bound it. */
    private static ExactRatio sum(List<TotalsASharingCanComeTo.Reach> reaches, int[] counts,
                                  ExactRatio total, boolean lower) {
        ExactRatio sum = ExactRatio.ZERO;
        for (int kind = 0; kind < reaches.size(); kind++) {
            List<TotalsASharingCanComeTo.Line> lines =
                    lower ? reaches.get(kind).lower() : reaches.get(kind).upper();
            if (lines.isEmpty()) {
                return null;
            }
            ExactRatio extreme = null;
            for (TotalsASharingCanComeTo.Line each : lines) {
                ExactRatio here = at(each, total);
                if (extreme == null || (here.compareTo(extreme) > 0) == lower) {
                    extreme = here;
                }
            }
            sum = sum.plus(extreme.times(ExactRatio.of(counts[kind])).orNull()).orNull();
        }
        return sum;
    }

    private static boolean canSumTo(List<TotalsASharingCanComeTo.Reach> reaches, int[] counts,
                                    ExactRatio total) {
        for (TotalsASharingCanComeTo.Reach each : reaches) {
            if ((each.totalLow() != null && total.compareTo(each.totalLow()) < 0)
                    || (each.totalHigh() != null && total.compareTo(each.totalHigh()) > 0)) {
                return false;
            }
        }
        ExactRatio least = sum(reaches, counts, total, true);
        ExactRatio most = sum(reaches, counts, total, false);
        return (least == null || least.compareTo(total) <= 0)
                && (most == null || most.compareTo(total) >= 0);
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
