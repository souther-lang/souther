package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comment inside a block body survives formatting. {@code block} walked only the block's child
 * nodes, so a comment explaining a step — the one place a body wants one — was dropped on the first
 * format. No example wrote one until a module with multi-step bodies did, and the formatter's own
 * round-trip test over the repository's {@code .sou} files caught it there.
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

    @Test
    void formattingIsStableOverABlockComment() {
        String once = Formatter.format(SOURCE);

        assertEquals(once, Formatter.format(once), "a second format changes nothing");
    }
}
