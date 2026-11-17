package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.UndividedByARelation.WholeEnds;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.NavigableSet;
import java.util.Optional;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@link RunOfASum} gives is the set of values some row takes, worked out by trying every row
 * of a small grid: a number from -2 to 2, none, one or two others of three kinds of ends, each
 * weighed one or minus one, and ends on the sum each missing or one of three. The grid holds
 * the ends that contradict each other, and the interval is the set exactly: a value left out is
 * taken by no row, and one in it is taken by some.
 */
class TheRunOfASumIsTheValuesSomeRowTakesTest {

    private static final WholeEnds MINE = ends(-2, 2);
    private static final WholeEnds[] OTHER_ENDS = {ends(0, 0), ends(-1, 1), ends(1, 2)};
    private static final Integer[] SUM_ENDS = {null, -3, 0, 2};

    @Test
    void theIntervalIsExactlyTheValuesAtWhichSomeRowsSumLiesBetweenTheEnds() {
        int empty = 0;
        int given = 0;
        for (int weight : new int[] {1, -1}) {
            for (List<RunOfASum.Other> others : everyOthers()) {
                for (Integer from : SUM_ENDS) {
                    for (Integer to : SUM_ENDS) {
                        Optional<WholeEnds> run = RunOfASum.of(MINE, big(weight), others,
                                from == null ? null : big(from), to == null ? null : big(to));
                        NavigableSet<Integer> taken = valuesSomeRowTakes(weight, others, from, to);
                        String at = "weight " + weight + " others " + others + " from " + from
                                + " to " + to;
                        if (taken.isEmpty()) {
                            assertTrue(run.isEmpty(), at + " gave " + run);
                            empty++;
                        } else {
                            assertEquals(Optional.of(ends(taken.first(), taken.last())), run, at);
                            assertEquals(taken.last() - taken.first() + 1, taken.size(), at);
                            given++;
                        }
                    }
                }
            }
        }
        // Both answers are met, or the sweep says nothing of the one that is not.
        assertTrue(empty > 100 && given > 100, empty + " empty, " + given + " given");
    }

    /** {@code x + n >= 1} and {@code x + n <= 0} leave no row: no value of {@code x} is taken. */
    @Test
    void endsOnTheSumThatContradictEachOtherLeaveNoValue() {
        assertTrue(RunOfASum.of(ends(-10, 10), big(1),
                List.of(new RunOfASum.Other(ends(-10, 10), big(1))), big(1), big(0)).isEmpty());
    }

    @Test
    void aWeightOtherThanOneOrMinusOneIsNotAsked() {
        assertTrue(RunOfASum.of(MINE, big(2), List.of(), big(0), big(1)).isEmpty());
        assertTrue(RunOfASum.of(MINE, big(1),
                List.of(new RunOfASum.Other(ends(0, 1), big(3))), big(0), big(1)).isEmpty());
        assertTrue(RunOfASum.of(MINE, big(1),
                List.of(new RunOfASum.Other(new WholeEnds(null, big(1)), big(1))), big(0), big(1))
                .isEmpty());
    }

    private static List<List<RunOfASum.Other>> everyOthers() {
        List<RunOfASum.Other> kinds = new ArrayList<>();
        for (WholeEnds each : OTHER_ENDS) {
            kinds.add(new RunOfASum.Other(each, big(1)));
            kinds.add(new RunOfASum.Other(each, big(-1)));
        }
        List<List<RunOfASum.Other>> out = new ArrayList<>();
        out.add(List.of());
        for (RunOfASum.Other one : kinds) {
            out.add(List.of(one));
            for (RunOfASum.Other two : kinds) {
                out.add(List.of(one, two));
            }
        }
        return out;
    }

    /** Every value of the number for which some value of each other brings the sum between the
     *  ends. */
    private static NavigableSet<Integer> valuesSomeRowTakes(int weight,
                                                            List<RunOfASum.Other> others,
                                                            Integer from, Integer to) {
        NavigableSet<Integer> out = new TreeSet<>();
        for (int v = MINE.low().intValue(); v <= MINE.high().intValue(); v++) {
            if (someOthersBring(weight * v, others, 0, from, to)) {
                out.add(v);
            }
        }
        return out;
    }

    private static boolean someOthersBring(int sum, List<RunOfASum.Other> others, int at,
                                           Integer from, Integer to) {
        if (at == others.size()) {
            return (from == null || sum >= from) && (to == null || sum <= to);
        }
        RunOfASum.Other each = others.get(at);
        for (int o = each.ends().low().intValue(); o <= each.ends().high().intValue(); o++) {
            if (someOthersBring(sum + each.weight().intValue() * o, others, at + 1, from, to)) {
                return true;
            }
        }
        return false;
    }

    private static WholeEnds ends(int low, int high) {
        return new WholeEnds(big(low), big(high));
    }

    private static BigInteger big(long value) {
        return BigInteger.valueOf(value);
    }
}
