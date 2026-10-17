package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.runtime.Strings;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The numbers a written text's code points are read as at compile time are the numbers
 * {@code String.codePoints} answers on a run, in the same order.
 *
 * <p>Over the texts where a count by UTF-16 unit and a count by code point part: one past the
 * basic plane, one a combining mark was composed into where the source was read, and none at all.
 */
class TheCodePointsOfAWrittenTextAreTheOnesARunAnswersTest {

    @Test
    void eachTextIsTheNumbersARunAnswers() {
        for (String text : List.of("0", "09", "😀", "a😀b", "é", "")) {
            List<Long> read = WrittenCodePoints.of(text, new SourcePos(1, 1)).stream()
                    .map(each -> ((Core.Int) each).value()).toList();
            assertEquals(Strings.codePoints(text), read, () -> "the code points of " + text);
        }
    }
}
