package souther.compiler.evaluate;

import org.junit.jupiter.api.Test;
import souther.runtime.Strings;
import souther.runtime.WorkCheckpoint;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An interrupt is a request that pure code never reads, so an evaluation whose caller gave up would
 * run for as long as the JVM lives. The counted points are where it reads the request.
 */
class AnEvaluationThatIsAbandonedStopsItselfTest {

    @Test
    void aCountedPointStopsTheEvaluationOnceItsThreadHasBeenInterrupted() {
        EvaluationContext.begin(1_000_000, 100);
        try {
            assertDoesNotThrow(EvaluationContext::tick);

            Thread.currentThread().interrupt();

            assertThrows(EvaluationAbandoned.class, EvaluationContext::tick);
            assertThrows(EvaluationAbandoned.class, EvaluationContext::enter);
        } finally {
            Thread.interrupted();
            EvaluationContext.end();
        }
    }

    /**
     * A runtime operation the evaluation called reads the request too, part of the way through: the
     * checkpoint it was handed is the evaluation's own.
     */
    @Test
    void aRuntimeOperationStopsOnceItsThreadHasBeenInterrupted() {
        String text = "a".repeat(100_000);
        EvaluationContext.begin(1_000_000_000L, 100);
        try {
            WorkCheckpoint checkpoint = EvaluationContext.checkpoint();
            assertEquals(100_000L, Strings.length(text, checkpoint));

            Thread.currentThread().interrupt();

            assertThrows(EvaluationAbandoned.class, () -> Strings.length(text, checkpoint));
        } finally {
            Thread.interrupted();
            EvaluationContext.end();
        }
    }

    /** And the steps it passes are spent from the same budget, so it stops when that is gone. */
    @Test
    void aRuntimeOperationStopsWhereTheEvaluationsStepsRunOut() {
        String text = "a".repeat(100_000);
        EvaluationContext.begin(1_000L, 100);
        try {
            assertThrows(StepLimitExceeded.class, () -> Strings.length(text, EvaluationContext.checkpoint()));
            assertEquals(1_000L, EvaluationContext.spent(1_000L));
        } finally {
            EvaluationContext.end();
        }
    }

    /** Work paid for at once is refused whole where the budget does not hold it, before any of it
     *  is done, and leaves the budget spent out as a pass past its end does. */
    @Test
    void workPaidForAtOnceIsRefusedWholeWhereTheBudgetDoesNotHoldIt() {
        EvaluationContext.begin(1_000L, 100);
        try {
            WorkCheckpoint checkpoint = EvaluationContext.checkpoint();
            checkpoint.spend(600L);
            assertEquals(600L, EvaluationContext.spent(1_000L));
            assertThrows(StepLimitExceeded.class, () -> checkpoint.spend(401L));
            assertEquals(1_000L, EvaluationContext.spent(1_000L));
        } finally {
            EvaluationContext.end();
        }
    }

    /** Between evaluations there is nothing to spend from, and a runtime operation handed what is
     *  there runs as a shipped class's does. */
    @Test
    void outsideAnEvaluationTheCheckpointIsTheOneNobodyHolds() {
        assertSame(WorkCheckpoint.NONE, EvaluationContext.checkpoint());
    }

    @Test
    void anAbandonedEvaluationIsOneThatRanOutAndNotAValueThatCannotBeBuilt() {
        assertTrue(EvaluationContext.overspending(EvaluationAbandoned.INSTANCE));
    }
}
