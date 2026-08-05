package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The command line answers for a source with a diagnostic and for itself with a report of its own.
 * A failure it never listed is the second kind: printing a stack trace at the author asks them to
 * read this compiler's call stack for a problem that is not theirs, and says nothing they can act on.
 * It is said as one line naming what was thrown, which is what a report of it would need.
 */
class ACompilerFailureNobodyListedIsNotAStackTraceTest {

    @Test
    void itNamesTheExceptionAndWhatItSaid() {
        String said = Main.internalFailure(new IllegalStateException("no pool to write into"));

        assertTrue(said.contains("internal compiler error"), said);
        assertTrue(said.contains("IllegalStateException"), said);
        assertTrue(said.contains("no pool to write into"), said);
        assertTrue(said.lines().count() == 1, "one line, not a stack trace: " + said);
    }

    @Test
    void anExceptionWithNothingToSayStillNamesItself() {
        String said = Main.internalFailure(new NullPointerException());

        assertTrue(said.contains("NullPointerException"), said);
    }

    @Test
    void aDiagnosticIsNotOneOfThese() {
        // a CompileException is the author's answer and is rendered as such wherever it is caught;
        // reaching this would mean reporting a diagnostic as a fault of the compiler
        assertNull(Main.internalFailure(CompileException.of(
                Diagnostic.literal(null, "E9999", "something about the source"),
                "something about the source")));
    }
}
