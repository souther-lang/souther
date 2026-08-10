package souther.compiler.check;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Region;

/**
 * A report about a value that did not fit points at the value, not at the form that asked for it.
 *
 * <p>The message names the operand in words — {@code argument 2 of String.append}, the text a
 * temporal was written as — and a reader who has the message still has to find the operand. Where
 * the caret sits under the form, that search crosses lines: an argument list has no bound on how far
 * its arguments are written from its callee, so the two can be a page apart. What the reader cannot
 * recover from the message is the operand, and that is what the caret is for.
 *
 * <p>Which region a report gets is not decided by its code. Three paths type a call — a kernel
 * applied against its declared signature, a helper expanded, a behavior called by name — and two of
 * them already answer with the argument. The rows below hold all three to one rule, so a path added
 * later is held to it too.
 */
class ADiagnosticPointsAtTheOperandThatSuppliedTheValueTest {

    /** The text {@code region} underlines, cut out of {@code source}. */
    private static String underlined(String source, Region region) {
        String line = source.split("\n", -1)[region.start().line() - 1];
        int from = region.start().column() - 1;
        int to = region.end().line() == region.start().line()
                ? region.end().column() - 1 : line.length();
        return line.substring(Math.min(from, line.length()), Math.min(to, line.length()));
    }

    private static Region regionOf(String source) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(source));
        return e.diagnostic().region();
    }

    /** The argument is written three lines below the callee, so nothing but the argument's own
     *  position puts the caret on a line the reader has to look at. */
    @Test
    void aKernelsArgumentIsUnderlinedWhereItIsWritten() {
        String source = """
                module demo

                behavior notice : (a: String, b: String) -> String

                let notice (a, b) =
                    String.append(
                        a,
                        String.length(b)
                    )
                """;

        assertEquals("String.length", underlined(source, regionOf(source)),
                "argument 2 is `String.length(b)` on line 8, not the callee on line 6");
    }

    /** A helper is expanded rather than applied, and answers with the argument already. */
    @Test
    void anExpandedHelpersArgumentIsPointedAtWhereItIsWritten() {
        String source = """
                module demo

                let shout (s: String): String = s

                behavior notice : (a: String) -> String

                let notice (a) =
                    shout(
                        String.length(a)
                    )
                """;

        assertEquals(9, regionOf(source).start().line(),
                "the argument is on line 9 and the callee on line 8");
    }

    /** A behavior is called against what it declares, and answers with the argument already. */
    @Test
    void aCalledBehaviorsArgumentIsUnderlinedWhereItIsWritten() {
        String source = """
                module demo

                behavior shout : (s: String) -> String

                behavior notice : (x: String) -> String
                    depends on shout

                let notice (x, shout) =
                    shout(
                        String.length(x)
                    )
                """;

        assertEquals("String.length", underlined(source, regionOf(source)),
                "argument 1 is `String.length(x)` on line 10, not the callee on line 9");
    }

    /** The text that would not parse is what the message quotes, so it is what the caret covers. */
    @Test
    void aTemporalThatWouldNotParseIsUnderlinedAtTheTextItWasWrittenAs() {
        String source = """
                module demo

                data Out = { on: Date }

                behavior closedOn : (n: Int) -> Out constructs Out

                let closedOn (n) = Out {
                    on = Date("2026-02-30")
                }
                """;

        assertEquals("\"2026-02-30\"", underlined(source, regionOf(source)),
                "the message quotes `2026-02-30`, so the caret covers it rather than `Date`");
    }
}
