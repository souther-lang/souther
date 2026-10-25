package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionBudget;
import souther.test.Nightly;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A library operation defined by its cases, over values no application of the closure is handed,
 * is split into them once for a table of as many constants as the readings figure allows with
 * two cases for each: the same cases on every application, each case another quantity, and so no
 * more lines on any one quantity than there are applications.
 *
 * <p>Nightly, for what it costs: the table is as long as the figure allows its cases to be
 * applied to, and saying where each of that many lines decides is most of a minute. A shorter
 * table is under the figure whether or not the readings are shared, so none asks the question
 * {@link AComparisonInAClosureIsReadOnceForTheWaysOfATotalThatDoesNotTurnOnTheElementTest} asks
 * of one that depends on the application.
 */
@Nightly
class ACaseOfAValueNoApplicationIsHandedIsSplitOnceForATableAsLongAsAnApplicationsCanBeTest {

    @Test
    void theCasesOfAnOperationOverTwoPositionsAreReadForEveryConstantOfTheTable() {
        int rows = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum() / 2 + 1;
        String report = AComparisonInAClosureIsReadOnceForTheWaysOfATotalThatDoesNotTurnOnTheElementTest
                .reachedBy("Int.max(w.first.pay, w.second.pay)", rows);
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
        assertTrue(report.contains("read as g/w.first.pay"), report);
    }
}
