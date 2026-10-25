package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The whole numbers a total is tried at are those of the interval the elements can sum to it in:
 * every one where it holds few, and otherwise the one nearest nought and the ones about each end —
 * said not to be all of them, so that a way tried at too few is never taken for one with none.
 */
class TheWholeNumbersATotalIsTriedAtAreTheNearestNoughtAndEachEndTest {

    private static TotalsASharingCanComeTo.Interval between(Long low, Long high) {
        return new TotalsASharingCanComeTo.Interval(low == null ? null : ExactRatio.of(low),
                high == null ? null : ExactRatio.of(high));
    }

    private static List<Long> tried(TotalsASharingCanComeTo.WholeNumbers found) {
        return found.tried().stream().map(BigInteger::longValue).toList();
    }

    @Test
    void anIntervalHoldingFewIsTriedAtEveryOneOfItsWholeNumbers() {
        TotalsASharingCanComeTo.WholeNumbers found =
                TotalsASharingCanComeTo.wholeNumbersIn(between(2L, 5L), 8);
        assertEquals(List.of(2L, 3L, 4L, 5L), tried(found).stream().sorted().toList());
        assertTrue(found.all());
        assertEquals(2L, tried(found).getFirst());
    }

    @Test
    void anIntervalAroundNoughtIsTriedAtNoughtFirst() {
        TotalsASharingCanComeTo.WholeNumbers found =
                TotalsASharingCanComeTo.wholeNumbersIn(between(-3L, 3L), 8);
        assertEquals(0L, tried(found).getFirst());
        assertTrue(found.all());
    }

    @Test
    void aWideIntervalIsTriedAtNoughtAndAboutEachEndAndIsNotAllOfThem() {
        TotalsASharingCanComeTo.WholeNumbers found =
                TotalsASharingCanComeTo.wholeNumbersIn(between(-1000L, 1000L), 8);
        assertEquals(8, found.tried().size());
        assertFalse(found.all());
        assertTrue(tried(found).contains(0L));
        assertTrue(tried(found).contains(-1000L));
        assertTrue(tried(found).contains(1000L));
    }

    @Test
    void anIntervalThatRunsOnIsTriedFromItsEndAndIsNotAllOfThem() {
        TotalsASharingCanComeTo.WholeNumbers found =
                TotalsASharingCanComeTo.wholeNumbersIn(between(5L, null), 8);
        assertEquals(5L, tried(found).getFirst());
        assertTrue(tried(found).stream().allMatch(each -> each >= 5L));
        assertFalse(found.all());
    }

    @Test
    void anIntervalBetweenTwoWholeNumbersHoldsNoneAndThatIsAllOfThem() {
        TotalsASharingCanComeTo.WholeNumbers found =
                TotalsASharingCanComeTo.wholeNumbersIn(new TotalsASharingCanComeTo.Interval(
                        ExactRatio.of(BigInteger.valueOf(1), BigInteger.valueOf(3)),
                        ExactRatio.of(BigInteger.valueOf(2), BigInteger.valueOf(3))), 8);
        assertEquals(List.of(), found.tried());
        assertTrue(found.all());
    }
}
