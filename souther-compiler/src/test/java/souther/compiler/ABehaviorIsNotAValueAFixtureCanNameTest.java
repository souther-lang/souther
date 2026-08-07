package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior taking nothing is implemented the way a value is. {@code behavior base : () -> Note} is
 * satisfied by {@code let base = Note { … }} — {@code let base ()} is not a parameter list a
 * definition may write (E2301) — so the definition behind a behavior and the definition behind a
 * value have the same shape, and nothing about the shape tells a fixture which it has.
 *
 * <p>What tells them apart is the table a fixture reads values from, which holds the module's
 * helpers and not its behaviors' implementations. Both positions a fixture may write a name in are
 * here: named where a value goes, and spread into a construction. The two used to disagree — the
 * name was refused by what it denotes and the spread was answered from the written module, which
 * holds the implementation the table leaves out.
 *
 * <p>A value of the same shape stands beside each, because a reading that refused by shape rather
 * than by what the table holds would refuse both.
 */
class ABehaviorIsNotAValueAFixtureCanNameTest {

    private static final String MODEL = """
            module demo

            data Note = { t: String }

            behavior base : () -> Note
                constructs Note

            let base = Note { t = "T" }

            let plain = Note { t = "T" }

            behavior echo : (n: Note) -> Note

            let echo (n) = n
            """;

    private static CompileException only(String rows) {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(MODEL + rows));
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        return e;
    }

    @Test
    void aBehaviorNamedWhereAValueGoesIsRefused() {
        CompileException e = only("""
                example echo
                  | (base) -> Note { t = "T" }
                """);
        Diagnostic d = e.diagnostics().get(0);

        assertEquals("E1903", d.code());
        assertTrue(e.getMessage().contains("`base` is not a value a fixture can name"),
                "the row is told the name is not a value, not that it built the wrong one: "
                        + e.getMessage());
    }

    @Test
    void aBehaviorSpreadIntoAConstructionIsRefused() {
        CompileException e = only("""
                example echo
                  | (Note { ...base }) -> Note { t = "T" }
                """);
        Diagnostic d = e.diagnostics().get(0);

        assertEquals("E1903", d.code());
        assertTrue(e.getMessage().contains("`base` is not a value a fixture can spread"),
                "a spread reads the table the same way a name does: " + e.getMessage());
    }

    @Test
    void aValueOfTheSameShapeIsNamed() {
        assertDoesNotThrow(() -> Compiler.compile(MODEL + """
                example echo
                  | (plain) -> Note { t = "T" }
                """));
    }

    @Test
    void aValueOfTheSameShapeIsSpread() {
        assertDoesNotThrow(() -> Compiler.compile(MODEL + """
                example echo
                  | (Note { ...plain }) -> Note { t = "T" }
                """));
    }
}
