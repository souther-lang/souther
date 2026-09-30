package souther.compiler.evaluate;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
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

    @Test
    void anAbandonedEvaluationIsOneThatRanOutAndNotAValueThatCannotBeBuilt() {
        assertTrue(EvaluationContext.overspending(EvaluationAbandoned.INSTANCE));
    }
}
