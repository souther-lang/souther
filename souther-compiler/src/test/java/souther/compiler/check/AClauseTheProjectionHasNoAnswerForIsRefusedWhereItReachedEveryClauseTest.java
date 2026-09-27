package souther.compiler.check;

import souther.compiler.core.BoundaryConstraint;
import souther.compiler.core.ConstraintProjection;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A clause the reading of constraints did not reach and a clause it has no answer for are two
 * things.
 *
 * <p>The first has nothing proved of it and is none. The second can only be the settled clauses and
 * the reading of them disagreeing about which clauses a data has, and answering it as the first
 * would turn that into a boundary that quietly reports every such clause under the shared code.
 */
class AClauseTheProjectionHasNoAnswerForIsRefusedWhereItReachedEveryClauseTest {

    private static final Clause.Id FIRST =
            new Clause.Id(TypeSymbols.declared(new TypeKey("m", "D")), 0);
    private static final Clause.Id SECOND =
            new Clause.Id(TypeSymbols.declared(new TypeKey("m", "D")), 1);

    private static final ConstraintProjection STATED =
            new ConstraintProjection(List.of(new BoundaryConstraint.MinLength(3)), true);

    @Test
    void aClauseTheReadingAnsweredIsItsAnswer() {
        assertEquals(STATED,
                new BoundaryConstraints.Projections(Map.of(FIRST, STATED), true).of(FIRST));
    }

    @Test
    void aClauseTheReadingDidNotReachIsNone() {
        assertEquals(ConstraintProjection.none(),
                new BoundaryConstraints.Projections(Map.of(FIRST, STATED), false).of(SECOND));
    }

    @Test
    void aClauseMissingFromAReadingThatReachedEveryClauseIsRefused() {
        BoundaryConstraints.Projections whole =
                new BoundaryConstraints.Projections(Map.of(FIRST, STATED), true);
        assertThrows(IllegalStateException.class, () -> whole.of(SECOND));
    }
}
