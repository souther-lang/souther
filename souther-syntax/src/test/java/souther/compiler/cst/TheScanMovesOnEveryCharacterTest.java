package souther.compiler.cst;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whatever the scan meets, it moves past.
 *
 * <p>A lexer that dispatches on one question and reads by another does not fail: it stops. The scan
 * asks what a character is, hands the text to the function for that kind, and that function reads
 * nothing — so the offset is where it was, the same character is met again, and the loop makes
 * empty tokens until the heap is gone. Nothing downstream sees a wrong answer, because nothing
 * downstream is reached.
 *
 * <p>So this is not a list of characters that once went wrong. Every kind the scan can dispatch to
 * is reached with characters chosen from the classes it dispatches on, in and outside the basic
 * plane, and what is asserted of each is what a scan that moved would leave: the text back, and no
 * token covering nothing.
 */
class TheScanMovesOnEveryCharacterTest {

    /** Long enough that a scan which is merely slow is not called stuck, short enough that a stuck
     *  one does not take the build with it. */
    private static final Duration BEFORE_IT_IS_STUCK = Duration.ofSeconds(5);

    @Test
    void andEveryCharacterOfWhatItReadIsInATokenOfIt() {
        List<String> stuck = new ArrayList<>();
        List<String> empty = new ArrayList<>();
        for (String written : written()) {
            CstLexer.Result lexed = assertTimeoutPreemptively(BEFORE_IT_IS_STUCK,
                    () -> CstLexer.lex(written),
                    () -> "the scan did not finish on " + shown(written));
            StringBuilder back = new StringBuilder();
            for (GreenToken token : lexed.tokens()) {
                back.append(token.text());
                if (token.text().isEmpty() && token.kind() != SyntaxKind.EOF) {
                    empty.add(shown(written) + " made a " + token.kind() + " covering nothing");
                }
            }
            if (!back.toString().equals(written)) {
                stuck.add(shown(written) + " came back as " + shown(back.toString()));
            }
        }
        assertEquals(List.of(), stuck, "the tokens do not join back into what was read");
        assertEquals(List.of(), empty, "a token covering nothing is a scan that did not move");
    }

    /**
     * What is written to the scan: every character the classes it dispatches on hold, one at a
     * time, and beside a letter — a character that stops a name is met in a different place from
     * one that begins the text.
     */
    private static List<String> written() {
        Set<Integer> points = new LinkedHashSet<>();
        for (int codePoint = 0; codePoint < 0x300; codePoint++) {
            points.add(codePoint);   // every character the language itself writes, and their neighbours
        }
        for (int codePoint = 0; codePoint <= Character.MAX_CODE_POINT; codePoint++) {
            // a digit of any script, which is the class the scan and the literal reader must agree
            // on, and the edges of the alphabet, which is the class the name reader answers for
            if (Character.isDigit(codePoint)
                    || IdentifierAlphabet.isStart(codePoint) != IdentifierAlphabet.isStart(codePoint + 1)
                    || IdentifierAlphabet.isContinue(codePoint)
                            != IdentifierAlphabet.isContinue(codePoint + 1)) {
                points.add(codePoint);
                points.add(codePoint + 1);
            }
        }
        points.remove(Character.MAX_CODE_POINT + 1);
        assertTrue(points.size() > 4000, "the classes were not swept: " + points.size());
        List<String> written = new ArrayList<>();
        for (int codePoint : points) {
            String one = new String(Character.toChars(codePoint));
            written.add(one);
            written.add("a" + one);
            written.add(one + "1");
        }
        return written;
    }

    private static String shown(String written) {
        StringBuilder out = new StringBuilder("`");
        written.codePoints().forEach(c -> out.append(String.format("\\x{%04X}", c)));
        return out.append("`").toString();
    }
}
