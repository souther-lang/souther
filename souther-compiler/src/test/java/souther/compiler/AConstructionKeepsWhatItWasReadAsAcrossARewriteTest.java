package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * One omission, two answers, decided by the reading the construction was read under and not by where
 * it stands when the question is asked.
 *
 * <p>A fixture leaves an optional field out and states the absent value the declaration holds; the
 * model's own construction gives every field a value, and leaving one out is a field with no value
 * (spec §example-evaluable, <<e1005>>). The reading settles which of the two a construction is held
 * to, and it is settled where the source is read.
 *
 * <p>The row here applies a helper inside its construction, which is what puts the construction
 * through a rewrite before the check reads it: expanding the call rebuilds the node the call stands
 * in. A rebuild that answered for the construction instead of carrying its answer would hold the row
 * to what a body is held to, and the omitted field would be reported as missing.
 */
class AConstructionKeepsWhatItWasReadAsAcrossARewriteTest {

    private static final String MODEL = """
            module demo

            data Note = { body: String, tag: String? }

            behavior keep : (n: Note) -> Note
                constructs Note

            let same (s: String) = s

            let keep (n) = Note { body = same(n.body), tag = n.tag }
            """;

    /**
     * The construction the row writes holds an application, so the expansion rebuilds it. What it
     * was read as is what decides the omitted {@code tag}, and it crossed the rebuild to get here.
     */
    @Test
    void aFixtureRebuiltByAnExpansionStillLeavesAnOptionalOut() {
        assertDoesNotThrow(() -> Compiler.compile(MODEL + """
                example keep
                  | "an omitted optional survives the expansion"
                      : (Note { body = same("b") }) -> Note { body = "b" }
                """));
    }

    /** The other answer, at the same declaration and the same field: what the model writes gives
     *  every field a value, so the same omission is the field with no value it is. */
    @Test
    void andTheModelsOwnConstructionMayNotLeaveOneOut() {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(MODEL + """
                        let incomplete (s: String) = Note { body = s }
                        """));

        assertEquals("E1005", refused.diagnostic().code(), refused.getMessage());
    }
}
