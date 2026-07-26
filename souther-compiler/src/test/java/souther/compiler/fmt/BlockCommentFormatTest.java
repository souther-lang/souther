package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Formatting a body that carries comments, in the shape a real module writes them. Where a comment
 * may go at all is enumerated by {@link CommentSurvivalTest}; this keeps the two multi-step bodies
 * that first exposed the problem, because they are what the repository's own `.sou` files look like.
 */
class BlockCommentFormatTest {

    private static final String SOURCE = """
            module demo

            data In = { n: Int }
            data Out = { n: Int }

            behavior run : (i: In) -> Out constructs Out

            let run (i) = {
                // why the doubling happens before anything else
                let doubled = i.n * 2
                // and why the result is built from it rather than from i
                Out { n = doubled }
            }
            """;

    @Test
    void aCommentInsideABlockBodyIsKept() {
        String formatted = Formatter.format(SOURCE);

        assertTrue(formatted.contains("// why the doubling happens before anything else"), formatted);
        assertTrue(formatted.contains("// and why the result is built from it rather than from i"),
                formatted);
    }

    private static final String IN_A_LITERAL = """
            module demo

            data In = { n: Int }
            data Out = { a: Int, b: Int }

            behavior run : (i: In) -> Out constructs Out

            let run (i) = Out {
                a = i.n,
                // why b is not simply a again
                b = i.n * 2
            }
            """;

    @Test
    void aCommentInsideARecordLiteralIsKept() {
        String formatted = Formatter.format(IN_A_LITERAL);

        assertTrue(formatted.contains("// why b is not simply a again"), formatted);
    }

    @Test
    void aCommentForcesTheLiteralToBreak() {
        // a `//` on a line the group had collapsed would swallow the rest of it, so the literal that
        // holds one is laid out a member per line
        String formatted = Formatter.format(IN_A_LITERAL);

        int comment = formatted.indexOf("// why b is not simply a again");
        int b = formatted.indexOf("b = i.n * 2");
        assertTrue(comment < b, formatted);
        assertTrue(formatted.substring(comment, b).contains("\n"),
                "the member starts on its own line: " + formatted);
    }

    @Test
    void twoCommentLinesKeepTheirOrder() {
        // each is prepended to the member, so building them one at a time reverses them — and a
        // reversal only shows on the second format, which is what the idempotency check catches
        String formatted = Formatter.format("""
                module demo

                data In = { n: Int }
                data Out = { a: Int, b: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    a = i.n,
                    // first line of the reason
                    // second line of the reason
                    b = i.n * 2
                }
                """);

        assertTrue(formatted.indexOf("// first line of the reason")
                < formatted.indexOf("// second line of the reason"), formatted);
        assertEquals(formatted, Formatter.format(formatted), "a second format changes nothing");
    }

    @Test
    void formattingIsStableOverALiteralComment() {
        String once = Formatter.format(IN_A_LITERAL);

        assertEquals(once, Formatter.format(once), "a second format changes nothing");
    }

    @Test
    void formattingIsStableOverABlockComment() {
        String once = Formatter.format(SOURCE);

        assertEquals(once, Formatter.format(once), "a second format changes nothing");
    }
}
