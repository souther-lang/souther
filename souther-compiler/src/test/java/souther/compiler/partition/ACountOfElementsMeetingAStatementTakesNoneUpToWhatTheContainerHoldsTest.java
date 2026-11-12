package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The count of the elements of a container that meet a statement is none up to how many the
 * container holds, whatever the least it holds is: a container of exactly two holds none, one or
 * two of the elements the statement holds of, and three of them is no count of it.
 */
class ACountOfElementsMeetingAStatementTakesNoneUpToWhatTheContainerHoldsTest {

    private static NumericDomain.Bounds between(long least, long most) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(least)),
                Endpoint.inclusive(Count.of(most)));
    }

    private static NumericDomain.Bounds from(long least) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(least)), null);
    }

    @Test
    void aContainerOfExactlyTwoHoldsNoneOneOrTwoAndNeverThree() {
        UndividedByARelation.CountTakes taken =
                UndividedByARelation.countTakes(between(2, 2), between(2, 2), true);
        for (long each : new long[] {0, 1, 2}) {
            assertTrue(taken.lies().admits(Count.of(each)), "lies at " + each);
            assertTrue(taken.takes().admits(Count.of(each)), "takes " + each);
        }
        assertFalse(taken.lies().admits(Count.of(3)));
        assertFalse(taken.takes().admits(Count.of(3)));
        assertFalse(taken.lies().admits(Count.of(-1)));
    }

    @Test
    void aContainerOfAtLeastTwoHoldsNoneAndOneToo() {
        UndividedByARelation.CountTakes taken =
                UndividedByARelation.countTakes(from(2), between(2, 10), true);
        assertTrue(taken.lies().admits(Count.of(0)));
        assertTrue(taken.lies().admits(Count.of(1_000_000)));
        assertTrue(taken.takes().admits(Count.of(0)));
        assertTrue(taken.takes().admits(Count.of(10)));
        assertFalse(taken.takes().admits(Count.of(11)));
    }

    @Test
    void nothingSaidOfHowManyItMayHoldLeavesTheCountLyingFromNoneOn() {
        UndividedByARelation.CountTakes taken =
                UndividedByARelation.countTakes(null, between(0, 3), true);
        assertTrue(taken.lies().admits(Count.of(0)));
        assertTrue(taken.lies().admits(Count.of(1_000)));
        assertFalse(taken.lies().admits(Count.of(-1)));
        assertFalse(taken.takes().admits(Count.of(4)));
    }

    /** A container that holds each element once shows the statement holding of one element and
     *  failing of another: the count is shown at none and one, however many it may hold. */
    @Test
    void aContainerThatHoldsEachElementOnceIsShownTheCountAtNoneAndOneOnly() {
        UndividedByARelation.CountTakes taken =
                UndividedByARelation.countTakes(from(0), between(0, 10), false);
        assertTrue(taken.lies().admits(Count.of(1_000)));
        assertTrue(taken.takes().admits(Count.of(0)));
        assertTrue(taken.takes().admits(Count.of(1)));
        assertFalse(taken.takes().admits(Count.of(2)));
        assertFalse(UndividedByARelation.countTakes(from(0), between(0, 0), false).takes()
                .admits(Count.of(1)));
    }

    /** A container that must hold two, each once, may hold only elements the statement holds of
     *  or only ones it fails of, and a row of one of each shows neither: the count is shown at
     *  one, and at none only where the container may be empty. */
    @Test
    void aContainerThatMustHoldElementsEachOnceIsNotShownTheCountAtNone() {
        UndividedByARelation.CountTakes taken =
                UndividedByARelation.countTakes(between(2, 2), between(2, 2), false);
        assertFalse(taken.takes().admits(Count.of(0)));
        assertTrue(taken.takes().admits(Count.of(1)));
        assertFalse(taken.takes().admits(Count.of(2)));
        assertTrue(taken.lies().admits(Count.of(0)));
    }
}
