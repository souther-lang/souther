package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * No clause in the list is two different news: the declarations were reached and state none, or a
 * declaration could not be reached and whatever it states is missing. Only the first says the value
 * is governed by nothing.
 */
class AnEmptyListOfClausesGovernsNothingOnlyWhereEveryRuleWasReachedTest {

    @Test
    void declarationsReachedThatStateNoClauseGovernNothing() {
        assertTrue(new ClausesInOrder(List.of(), true).governsNothing());
    }

    @Test
    void aDeclarationThatCouldNotBeReachedMayStillGovernTheValue() {
        assertFalse(new ClausesInOrder(List.of(), false).governsNothing());
    }
}
