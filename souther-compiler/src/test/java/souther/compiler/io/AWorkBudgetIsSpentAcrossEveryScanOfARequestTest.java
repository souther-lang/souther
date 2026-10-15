package souther.compiler.io;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/** A limit on one scan says nothing about how many scans a request makes; the budget is for all of them. */
class AWorkBudgetIsSpentAcrossEveryScanOfARequestTest {

    @Test
    void unitsSpentInDifferentPlacesAreSpentFromTheOneBudget() throws Exception {
        WorkBudget budget = WorkBudget.of(10);

        budget.spend(4);
        budget.spend(6);

        assertThrows(LimitExceededException.class, () -> budget.spend(1));
    }

    @Test
    void aSpendBeyondTheBudgetLeavesNothingForTheNextOne() {
        WorkBudget budget = WorkBudget.of(10);

        assertThrows(LimitExceededException.class, () -> budget.spend(11));

        assertThrows(LimitExceededException.class, () -> budget.spend(1));
    }

    @Test
    void aSpendThatExactlyUsesItUpIsAllowed() {
        WorkBudget budget = WorkBudget.of(3);

        assertDoesNotThrow(() -> budget.spend(3));
    }
}
