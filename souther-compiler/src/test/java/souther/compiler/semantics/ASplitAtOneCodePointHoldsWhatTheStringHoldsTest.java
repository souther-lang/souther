package souther.compiler.semantics;

import org.junit.jupiter.api.Test;

import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Some piece of a string split at one code point holding a code point of a class is the string
 * holding one that is in the class and is not that code point — checked against what the run time
 * answers rather than against the statement of it.
 *
 * <p>Every string up to a length over an alphabet that has what could part the two: the separator,
 * the whitespace the library trims at either end and at no other — the ideographic space and the
 * no-break space beside the plain one — a control character that is not whitespace, a code point
 * outside the basic plane, and plain letters. A law that held of the strings a person would write
 * and failed at a string of separators and whitespace alone would be right where nobody looked.
 */
class ASplitAtOneCodePointHoldsWhatTheStringHoldsTest {

    private static final List<String> ALPHABET = List.of(
            ",", " ", "　", " ", "\u0007", "😀", "a", "B");

    private static final int LONGEST = 5;

    /** Every string of the alphabet's letters up to {@code LONGEST} of them. */
    private static List<String> strings() {
        List<String> out = new ArrayList<>(List.of(""));
        List<String> last = List.of("");
        for (int length = 1; length <= LONGEST; length++) {
            List<String> next = new ArrayList<>();
            for (String each : last) {
                for (String letter : ALPHABET) {
                    next.add(each + letter);
                }
            }
            out.addAll(next);
            last = next;
        }
        return out;
    }

    /**
     * Some piece that trims to something is some code point of the string that is neither
     * whitespace nor the separator — which is what a trimmed piece holding something comes to
     * once the pieces are put together.
     */
    @Test
    void somePieceThatTrimsToSomethingIsACodePointThatIsNeitherWhitespaceNorTheSeparator() {
        CodePointClass outside = new CodePointClass.NotWhitespaceNorEqualTo(',');
        int checked = 0;
        for (String each : strings()) {
            boolean somePiece = Strings.split(each, ",").stream()
                    .anyMatch(piece -> !Strings.trim(piece).isEmpty());
            boolean stringHoldsOne = each.codePoints().anyMatch(outside::contains);
            assertEquals(somePiece, stringHoldsOne, "of " + show(each));
            checked++;
        }
        assertTrue(checked > 30_000, "every string there is was asked, and " + checked + " were");
    }

    /** And the same of a piece holding any code point that is not whitespace, with no trimming. */
    @Test
    void somePieceHoldingACodePointThatIsNotWhitespaceIsTheStringHoldingOneBesidesTheSeparator() {
        CodePointClass notWhitespace = new CodePointClass.NotWhitespace();
        CodePointClass outside = new CodePointClass.NotWhitespaceNorEqualTo(',');
        for (String each : strings()) {
            boolean somePiece = Strings.split(each, ",").stream()
                    .anyMatch(piece -> piece.codePoints().anyMatch(notWhitespace::contains));
            assertEquals(somePiece, each.codePoints().anyMatch(outside::contains),
                    "of " + show(each));
        }
    }

    /**
     * Where the separator is itself whitespace the two classes are one, which is what a class
     * leaving it out leaves out of what is not whitespace.
     */
    @Test
    void aSeparatorThatIsWhitespaceLeavesNothingOutOfWhatIsNotWhitespace() {
        CodePointClass notWhitespace = new CodePointClass.NotWhitespace();
        CodePointClass outside = new CodePointClass.NotWhitespaceNorEqualTo(' ');
        for (String each : strings()) {
            boolean somePiece = Strings.split(each, " ").stream()
                    .anyMatch(piece -> piece.codePoints().anyMatch(notWhitespace::contains));
            assertEquals(somePiece, each.codePoints().anyMatch(outside::contains),
                    "of " + show(each));
        }
    }

    /**
     * A separator longer than one code point is the case the law is not about: the pieces of
     * {@code "abab"} split at {@code "ab"} are three empty ones, while the string holds code
     * points that are neither whitespace nor either of the separator's.
     */
    @Test
    void aSeparatorOfSeveralCodePointsIsNotWhatTheLawIsAbout() {
        assertEquals(List.of("", "", ""), Strings.split("abab", "ab"));
        CodePointClass outside = new CodePointClass.NotWhitespaceNorEqualTo('a');
        assertTrue("abab".codePoints().anyMatch(outside::contains),
                "the string holds a code point that is neither whitespace nor an a, and no piece"
                        + " holds anything");
    }

    private static String show(String text) {
        StringBuilder out = new StringBuilder("\"");
        text.codePoints().forEach(cp -> out.append(cp > 32 && cp < 127
                ? String.valueOf((char) cp) : "U+%X".formatted(cp)));
        return out.append('"').toString();
    }
}
