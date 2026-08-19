package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A temporal is shown the way a model writes one, wherever it is shown.
 *
 * <p>A boundary label, a generated row and the value a mismatch reports are three places one time of
 * day is written, and a reader compares them against each other. {@code LocalTime.toString} drops
 * seconds at zero and {@code LocalDateTime.toString} does the same, so what came back was written
 * {@code Time("16:00")} beside a line the same value named {@code Time("16:00:00")} — one value
 * shown two ways, in the one report where the two are meant to be read together.
 *
 * <p>Which is the reason the writers spell the seconds out, said at the other end of the same
 * report. A rule stated in one place and not asked at the other is a rule about one of the paths.
 */
class ATemporalIsShownTheWayItIsWrittenTest {

    private static Diagnostic only(String model) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(model));
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        return e.diagnostics().get(0);
    }

    /** A time of day whose seconds are zero, which is the value a line is most often drawn at. */
    @Test
    void aTimeIsShownToTheSecond() {
        Diagnostic d = only("""
                module demo

                data In = { n: Int }

                behavior at : (i: In) -> Time

                let at (i) = Time("16:00:00")

                example at
                    | "the wrong answer" : (In { n = 1 }) -> Time("17:00:00")
                """);

        assertEquals("E1905", d.code());
        assertEquals("Time(\"16:00:00\")", d.diff().actualType(),
                "what came back is written the way the model wrote it");
        assertEquals("Time(\"17:00:00\")", d.diff().expectedType());
    }

    /** And a date-time, which drops its seconds the same way. */
    @Test
    void aDateTimeIsShownToTheSecond() {
        Diagnostic d = only("""
                module demo

                data In = { n: Int }

                behavior at : (i: In) -> DateTime

                let at (i) = DateTime("2026-08-01T16:00:00")

                example at
                    | "the wrong answer" : (In { n = 1 }) -> DateTime("2026-08-01T17:00:00")
                """);

        assertEquals("E1905", d.code());
        assertEquals("DateTime(\"2026-08-01T16:00:00\")", d.diff().actualType());
        assertEquals("DateTime(\"2026-08-01T17:00:00\")", d.diff().expectedType());
    }
}
