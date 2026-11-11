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
                UndividedByARelation.countTakes(between(2, 2), between(2, 2));
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
                UndividedByARelation.countTakes(from(2), between(2, 10));
        assertTrue(taken.lies().admits(Count.of(0)));
        assertTrue(taken.lies().admits(Count.of(1_000_000)));
        assertTrue(taken.takes().admits(Count.of(0)));
        assertTrue(taken.takes().admits(Count.of(10)));
        assertFalse(taken.takes().admits(Count.of(11)));
    }

    @Test
    void nothingSaidOfHowManyItMayHoldLeavesTheCountLyingFromNoneOn() {
        UndividedByARelation.CountTakes taken =
                UndividedByARelation.countTakes(null, between(0, 3));
        assertTrue(taken.lies().admits(Count.of(0)));
        assertTrue(taken.lies().admits(Count.of(1_000)));
        assertFalse(taken.lies().admits(Count.of(-1)));
        assertFalse(taken.takes().admits(Count.of(4)));
    }
}
