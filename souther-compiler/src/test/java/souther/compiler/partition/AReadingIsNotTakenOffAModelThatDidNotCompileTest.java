package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import org.opentest4j.AssertionFailedError;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading of a decision is refused for a model the compile found an error in, though only what
 * the reading is read off is asked ({@link DecisionReadings}): an error in checking a body, and a
 * construction a behavior declares and never makes, are each found on the way to the reading.
 */
class AReadingIsNotTakenOffAModelThatDidNotCompileTest {

    private static final String MODEL = """
            module refused

            data Seen = { hit: Bool }

            behavior f : (n: Int) -> Seen
                constructs Seen
            let f (n) = Seen { hit = n > 0 }
            """;

    @Test
    void theControlIsRead() {
        assertTrue(DecisionReadings.of(MODEL, "f") != null);
    }

    @Test
    void aBodyThatDoesNotCheckIsRefused() {
        assertThrows(AssertionFailedError.class,
                () -> DecisionReadings.of(MODEL.replace("n > 0", "n + \"x\""), "f"));
    }

    @Test
    void aConstructionDeclaredAndNeverMadeIsRefused() {
        assertThrows(AssertionFailedError.class, () -> DecisionReadings.of(MODEL
                .replace("-> Seen", "-> Bool").replace("Seen { hit = n > 0 }", "n > 0"), "f"));
    }
}
