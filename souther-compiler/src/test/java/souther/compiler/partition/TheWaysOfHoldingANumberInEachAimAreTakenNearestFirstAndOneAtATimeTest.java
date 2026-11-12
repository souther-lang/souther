package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.TermPath;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The ways of taking one number of each aim of a parameter are every way, and the nearest to every
 * first number come first: a record whose rules allow only some pairing of the numbers of its
 * collections is answered by the way that is allowed, which no fixed pairing of the numbers
 * reaches. They are as many as the numbers of each multiplied, so they are made one at a time and
 * no further than the search goes on.
 */
class TheWaysOfHoldingANumberInEachAimAreTakenNearestFirstAndOneAtATimeTest {

    private static RowAims.Aim aim(String field, int numbers) {
        List<BigInteger> of = new ArrayList<>();
        for (int at = 0; at < numbers; at++) {
            of.add(BigInteger.valueOf(at));
        }
        return new RowAims.Aim(TermPath.of("p").then(field), of);
    }

    private static List<List<Integer>> waysOf(List<RowAims.Aim> aims, int atMost) {
        List<List<Integer>> ways = new ArrayList<>();
        RowSearch.nearestFirst(aims, picks -> {
            ways.add(java.util.Arrays.stream(picks).boxed().toList());
            return ways.size() < atMost;
        });
        return ways;
    }

    /** By what the places add up to, and for the same sum in the order the aims stand in. */
    @Test
    void everyWayIsMadeTheNearestToEveryFirstNumberFirst() {
        assertEquals(List.of(
                        List.of(0, 0), List.of(0, 1), List.of(1, 0), List.of(1, 1), List.of(2, 0),
                        List.of(2, 1)),
                waysOf(List.of(aim("xs", 3), aim("ys", 2)), Integer.MAX_VALUE));
    }

    /** No way is made twice and none is left out: the ways are the product of the numbers. */
    @Test
    void theWaysAreTheProductOfTheNumbersOfEachAim() {
        List<List<Integer>> ways = waysOf(List.of(aim("a", 2), aim("b", 4), aim("c", 3)),
                Integer.MAX_VALUE);
        assertEquals(24, ways.size());
        assertEquals(24, ways.stream().distinct().count());
    }

    /** Asked for no more, no more are made: nine aims of four numbers are four to the ninth. */
    @Test
    void waysNobodyAsksForAreNotMade() {
        List<RowAims.Aim> many = new ArrayList<>();
        for (int at = 0; at < 9; at++) {
            many.add(aim("f" + at, 4));
        }
        List<List<Integer>> ways = waysOf(many, 10);
        assertEquals(10, ways.size());
        assertEquals(List.of(0, 0, 0, 0, 0, 0, 0, 0, 0), ways.getFirst());
    }
}
