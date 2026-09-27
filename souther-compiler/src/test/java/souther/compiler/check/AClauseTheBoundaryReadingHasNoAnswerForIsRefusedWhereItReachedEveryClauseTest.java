package souther.compiler.check;

import souther.compiler.core.BoundaryCheck;
import souther.compiler.core.BoundaryConstraint;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A clause the boundary's reading did not reach and a clause it has no answer for are two things.
 *
 * <p>The first has nothing proved of it and is checked as its condition. The second can only be the
 * settled clauses and the reading of them disagreeing about which clauses a data has, and answering
 * it as the first would turn that into a boundary that quietly reports every such clause under the
 * shared code.
 */
class AClauseTheBoundaryReadingHasNoAnswerForIsRefusedWhereItReachedEveryClauseTest {

    private static final Clause.Id FIRST =
            new Clause.Id(TypeSymbols.declared(new TypeKey("m", "D")), 0);
    private static final Clause.Id SECOND =
            new Clause.Id(TypeSymbols.declared(new TypeKey("m", "D")), 1);

    private static final BoundaryCheck STATED =
            new BoundaryCheck(List.of(new BoundaryConstraint.MinLength(3)), false);

    @Test
    void aClauseTheReadingAnsweredIsItsAnswer() {
        assertEquals(STATED, new BoundaryConstraints.Checks(Map.of(FIRST, STATED), true).of(FIRST));
    }

    @Test
    void aClauseTheReadingDidNotReachIsItsCondition() {
        assertEquals(BoundaryCheck.conditionOnly(),
                new BoundaryConstraints.Checks(Map.of(FIRST, STATED), false).of(SECOND));
    }

    @Test
    void aClauseMissingFromAReadingThatReachedEveryClauseIsRefused() {
        BoundaryConstraints.Checks whole = new BoundaryConstraints.Checks(Map.of(FIRST, STATED), true);
        assertThrows(IllegalStateException.class, () -> whole.of(SECOND));
    }
}
