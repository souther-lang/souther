package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.SourceSpace;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the formatter takes for the space around a token is what the lexer reads as that: a space,
 * a tab, a carriage return or a line feed. An ideographic space ending a comment is part of what
 * the comment says, and formatting keeps it; the spaces a source is laid out in after it are not,
 * and formatting drops them.
 */
class ACommentKeepsTheWhiteSpaceThatIsNotASourcesTest {

    @Test
    void anIdeographicSpaceEndingACommentIsKept() {
        String formatted = Formatter.format("module m\n// 注記　  \ndata D = { a: Int }\n");
        assertTrue(formatted.contains("// 注記　\n"), formatted);
    }

    @Test
    void theSpaceBetweenTokensIsTheLexersFour() {
        for (char each : new char[] {' ', '\t', '\r', '\n'}) {
            assertTrue(SourceSpace.is(each), () -> "U+" + Integer.toHexString(each));
        }
        for (int each : new int[] {0x3000, 0x00A0, 0x000B, 0x000C, 0x2028, 0x1680}) {
            assertFalse(SourceSpace.is(each), () -> "U+" + Integer.toHexString(each));
        }
        assertEquals("　a　", SourceSpace.strip(" \t　a　\r\n"));
    }
}
