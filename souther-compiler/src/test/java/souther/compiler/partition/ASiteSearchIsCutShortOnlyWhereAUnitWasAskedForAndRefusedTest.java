package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The figure a site is searched by is spent a unit at a time. That a search used the last of it and
 * was done says nothing of whether it left anything, so it is not said to be cut short; one that
 * asked for a unit there was none of, or left something undone for want of one, is.
 */
class ASiteSearchIsCutShortOnlyWhereAUnitWasAskedForAndRefusedTest {

    @Test
    void aSearchThatSpentTheLastUnitAndWasDoneIsNotCutShort() {
        StopAssessment.Tries tries = new StopAssessment.Tries(3);
        assertTrue(tries.spend() && tries.spend() && tries.spend());
        assertTrue(tries.spent());
        assertFalse(tries.cutShort());
    }

    @Test
    void aSearchThatAskedForAUnitThereWasNoneOfIsCutShort() {
        StopAssessment.Tries tries = new StopAssessment.Tries(1);
        assertTrue(tries.spend());
        assertFalse(tries.spend());
        assertTrue(tries.cutShort());
    }

    @Test
    void aSearchThatLeftSomethingUndoneIsCutShort() {
        StopAssessment.Tries tries = new StopAssessment.Tries(3);
        tries.leftSomethingUndone();
        assertTrue(tries.cutShort());
    }
}
