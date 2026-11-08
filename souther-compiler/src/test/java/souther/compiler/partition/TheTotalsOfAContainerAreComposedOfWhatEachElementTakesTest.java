package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;

import java.util.HashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * The totals a container of elements each taking every value of a run comes to, for as many
 * elements as it may hold ({@link UndividedByARelation#overTheCounts}), held to the totals
 * themselves: every whole number the claimed run holds is a total of so many values of the run,
 * for some count the container may hold. A gap between two counts' totals is never claimed.
 */
class TheTotalsOfAContainerAreComposedOfWhatEachElementTakesTest {

    private static final int MOST = 7;

    @Test
    void everyTotalClaimedIsOneSoManyElementsComeTo() {
        int claimedPastOne = 0;
        for (int a = -5; a <= 6; a++) {
            for (int b = a; b <= 6; b++) {
                for (int fewest = 0; fewest <= 2; fewest++) {
                    for (int most = Math.max(1, fewest); most <= MOST; most++) {
                        NumericDomain.Bounds claimed = UndividedByARelation.overTheCounts(
                                run(a, b), run(fewest, most), Carrier.WHOLE);
                        if (claimed == null) {
                            continue;
                        }
                        Set<Long> totals = totals(a, b, fewest, most);
                        long low = end(claimed.min());
                        long high = end(claimed.max());
                        for (long t = low; t <= high; t++) {
                            if (!totals.contains(t)) {
                                fail("[" + a + ", " + b + "] over " + fewest + ".." + most
                                        + " claims " + claimed + ", and no total is " + t);
                            }
                        }
                        if (high - low > b - a) {
                            claimedPastOne++;
                        }
                    }
                }
            }
        }
        assertNotEquals(0, claimedPastOne, "some run is claimed past one element's");
    }

    /** Elements at three or four come to three or four, then six to eight, then nine on with no
     *  gap: five is no total, and the run claimed is the one from six on. */
    @Test
    void aGapBetweenTwoCountsIsNotTaken() {
        NumericDomain.Bounds claimed = UndividedByARelation.overTheCounts(run(3, 4),
                new NumericDomain.Bounds(inclusive(0), null), Carrier.WHOLE);
        assertEquals(new NumericDomain.Bounds(inclusive(6), null), claimed);
        assertFalse(claimed.admits(Count.of(5)));
    }

    /** Elements at two come to the even numbers only, and the run of one element is all that is
     *  claimed. */
    @Test
    void aRunOfOneValueIsNoRunOfItsMultiples() {
        assertEquals(run(2, 2), UndividedByARelation.overTheCounts(run(2, 2),
                new NumericDomain.Bounds(inclusive(0), null), Carrier.WHOLE));
    }

    /** From nought to a hundred each, any number of elements comes to every whole number from
     *  nought on; and from minus one on, to every whole number. */
    @Test
    void aRunHoldingNoughtReachesAsFarAsTheCountsGo() {
        NumericDomain.Bounds anyMany = new NumericDomain.Bounds(inclusive(0), null);
        assertEquals(new NumericDomain.Bounds(inclusive(0), null),
                UndividedByARelation.overTheCounts(run(0, 100), anyMany, Carrier.WHOLE));
        assertEquals(NumericDomain.Bounds.OPEN, UndividedByARelation.overTheCounts(
                new NumericDomain.Bounds(inclusive(-1), null), anyMany, Carrier.WHOLE));
        assertEquals(run(0, 300),
                UndividedByARelation.overTheCounts(run(0, 100), run(0, 3), Carrier.WHOLE));
    }

    /** A run of whole numbers left open at an end is taken at the whole numbers it holds: two
     *  elements past nought come to two at the least. */
    @Test
    void anEndLeftOutIsTakenAtTheWholeNumberInside() {
        NumericDomain.Bounds pastNought = new NumericDomain.Bounds(
                new Endpoint(Count.of(0), false), inclusive(1));
        NumericDomain.Bounds claimed = UndividedByARelation.overTheCounts(pastNought, run(2, 2),
                Carrier.WHOLE);
        assertEquals(run(2, 2), claimed);
    }

    /** Over values with none between them, runs past nought meet once their widths make up the
     *  distance from nought: one to two each meet two to four at two. Meeting at a value both
     *  runs leave out is no meeting: between one and two each, two is a total of no list. */
    @Test
    void runsOfDecimalsMeetWithoutAStep() {
        NumericDomain.Bounds anyMany = new NumericDomain.Bounds(inclusive(0), null);
        assertEquals(new NumericDomain.Bounds(inclusive(1), null),
                UndividedByARelation.overTheCounts(run(1, 2), anyMany, Carrier.DENSE));
        NumericDomain.Bounds open = new NumericDomain.Bounds(new Endpoint(Count.of(1), false),
                new Endpoint(Count.of(2), false));
        NumericDomain.Bounds claimed = UndividedByARelation.overTheCounts(open, anyMany,
                Carrier.DENSE);
        assertTrue(claimed != null && !claimed.admits(Count.of(2)), String.valueOf(claimed));
        NumericDomain.Bounds halfOpen = new NumericDomain.Bounds(
                new Endpoint(Count.of(1), false), inclusive(2));
        assertEquals(new NumericDomain.Bounds(new Endpoint(Count.of(1), false), null),
                UndividedByARelation.overTheCounts(halfOpen, anyMany, Carrier.DENSE));
    }

    private static Set<Long> totals(int a, int b, int fewest, int most) {
        Set<Long> out = new HashSet<>();
        Set<Long> ofN = new HashSet<>(Set.of(0L));
        for (int n = 1; n <= most; n++) {
            Set<Long> next = new HashSet<>();
            for (long sofar : ofN) {
                for (int v = a; v <= b; v++) {
                    next.add(sofar + v);
                }
            }
            ofN = next;
            if (n >= fewest) {
                out.addAll(ofN);
            }
        }
        return out;
    }

    private static NumericDomain.Bounds run(long low, long high) {
        return new NumericDomain.Bounds(inclusive(low), inclusive(high));
    }

    private static Endpoint inclusive(long at) {
        return Endpoint.inclusive(Count.of(at));
    }

    private static long end(Endpoint end) {
        return Count.number(end.at()).at().longValueExact();
    }
}
