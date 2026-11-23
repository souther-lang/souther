package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A library operation defined by its cases, over values no application of the closure is handed,
 * is split into them once for a table of as many constants as the readings figure allows with
 * two cases for each: the same cases on every application, each case another quantity, and so no
 * more lines on any one quantity than there are applications.
 *
 * <p>The figure is the one the compilations of
 * {@link AComparisonInAClosureIsReadOnceForTheWaysOfATotalThatDoesNotTurnOnTheElementTest} are
 * held to, and the table is the shortest one whose cases, split again on every application, would
 * be more readings than that. A shorter table is under the figure whether or not the readings are
 * shared, so none asks the question that test asks of one that depends on the application.
 */
class ACaseOfAValueNoApplicationIsHandedIsSplitOnceForATableAsLongAsAnApplicationsCanBeTest {

    @Test
    void theCasesOfAnOperationOverTwoPositionsAreReadForEveryConstantOfTheTable() {
        int rows = AComparisonInAClosureIsReadOnceForTheWaysOfATotalThatDoesNotTurnOnTheElementTest.MOST
                / 2 + 1;
        String report = AComparisonInAClosureIsReadOnceForTheWaysOfATotalThatDoesNotTurnOnTheElementTest
                .reachedBy("Int.max(w.first.pay, w.second.pay)", rows);
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
        assertTrue(report.contains("read as g/w.first.pay"), report);
    }
}
