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
 * <p>The figure is held to {@link #MOST}, and the table is the shortest one whose cases, split
 * again on every application, would be more readings than that. A shorter table is under the
 * figure whether or not the readings are shared, so none asks the question
 * {@link AComparisonInAClosureIsReadOnceForTheWaysOfATotalThatDoesNotTurnOnTheElementTest} asks
 * of one that depends on the application.
 */
class ACaseOfAValueNoApplicationIsHandedIsSplitOnceForATableAsLongAsAnApplicationsCanBeTest {

    /** The readings of one condition the compilation is held to: the fewest the rest of the body
     *  is read within, so that only splitting the cases on every application could reach it. */
    private static final int MOST = 8;

    @Test
    void theCasesOfAnOperationOverTwoPositionsAreReadForEveryConstantOfTheTable() {
        String report = AComparisonInAClosureIsReadOnceForTheWaysOfATotalThatDoesNotTurnOnTheElementTest
                .reachedBy("Int.max(w.first.pay, w.second.pay)", MOST / 2 + 1, MOST);
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
        assertTrue(report.contains("read as g/w.first.pay"), report);
    }
}
