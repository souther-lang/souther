package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.text.StringWhitespace;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The String whitespace the grammar refuses a row's name for is the set {@code trim} takes off.
 *
 * <p>The syntax cannot see the run time, so each holds the set; this is what holds them to each
 * other. Asked of every scalar value, through what the run time offers a program rather than its
 * private table: a character is whitespace where {@code trim} leaves nothing of it.
 */
class TheGrammarsStringWhitespaceIsTheRunTimesTest {

    @Test
    void everyScalarValueIsWhitespaceToBothOrToNeither() {
        List<String> apart = new ArrayList<>();
        int whitespace = 0;
        for (int codePoint = 0; codePoint <= Character.MAX_CODE_POINT; codePoint++) {
            if (codePoint >= Character.MIN_SURROGATE && codePoint <= Character.MAX_SURROGATE) {
                continue;
            }
            boolean grammar = StringWhitespace.isWhitespace(codePoint);
            boolean runTime = Strings.trim(Character.toString(codePoint)).isEmpty();
            if (grammar != runTime) {
                apart.add(String.format("U+%04X", codePoint));
            }
            if (grammar) {
                whitespace++;
            }
        }
        assertEquals(List.of(), apart);
        assertEquals(25, whitespace, "the specification's set, so neither side is empty");
    }
}
