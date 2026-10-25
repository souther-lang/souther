package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What was found among a record's rules is no account of what it declares: a declaration whose
 * rules could not be expanded lists none of them, and a rule nothing was made of leaves no
 * statement, and neither is a record with no rule.
 *
 * <p>The cases are built from the parts and not from a source: a declaration that cannot be
 * expanded is one the compiler refuses before anything here reads it, so there is no source that
 * reaches the state, and the state is what a reader is held to answering correctly all the same.
 */
class ARecordWhoseRulesWereNotAllReachedIsNotOneWithNoRuleTest {

    @Test
    void nothingListedAndNothingLeftOutIsNoRule() {
        RecordRules none = new RecordRules(Map.of(), List.of(), 0, 0, true, List.of());

        assertTrue(none.declaresNothing());
        assertTrue(none.readInFull());
    }

    @Test
    void nothingListedBecauseTheRulesWereNotReachedIsNotNoRule() {
        RecordRules unreached = new RecordRules(Map.of(), List.of(), 0, 0, false, List.of());

        assertFalse(unreached.declaresNothing());
        assertFalse(unreached.readInFull());
    }

    @Test
    void aRuleNothingWasMadeOfIsARuleAndIsNotRead() {
        RecordRules unread = new RecordRules(Map.of(), List.of(), 1, 1, true, List.of());

        assertFalse(unread.declaresNothing());
        assertFalse(unread.readInFull());
    }

    @Test
    void aNameWhoseRulesWereNotReachedCarriesNoneOnlyWhereTheyWereAllReached() {
        TypeSymbol worn = null;

        assertTrue(new DeclaredClauses.OnAName(worn, List.of(), true).carriesNone());
        assertFalse(new DeclaredClauses.OnAName(worn, List.of(), false).carriesNone());
    }
}
