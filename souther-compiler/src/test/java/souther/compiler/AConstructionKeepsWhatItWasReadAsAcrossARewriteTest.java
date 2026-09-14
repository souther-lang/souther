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
 * <p>Every construction is rebuilt between the two: the newtype desugaring walks each one and puts
 * back what it found, so nothing has to be arranged for the answer to have crossed a rewrite by the
 * time the check reads it. A rebuild that answered for the construction instead of carrying what it
 * was handed would hold the row to what a body is held to, and the omitted field would be reported
 * as missing.
 *
 * <p>The pair is what this holds, and it is one declaration and one field: the same omission, read
 * two ways. That a rebuild carries the answer at all is held wherever a fixture omits an optional,
 * which is not this test's to say again.
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

    /** What the fixture was read as is what decides the omitted {@code tag}, and it is read off the
     *  construction after every rewrite between the reading and the check. */
    @Test
    void aFixtureRebuiltOnItsWayToTheCheckStillLeavesAnOptionalOut() {
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
