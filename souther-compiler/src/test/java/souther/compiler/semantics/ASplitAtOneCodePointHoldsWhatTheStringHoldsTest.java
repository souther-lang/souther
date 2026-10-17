package souther.compiler.semantics;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.ValueName;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Some piece of a string split at one code point holding a code point of a class is the string
 * holding one that is in the class and is not that code point, and there is one more piece than
 * the times the code point stands in the string — checked against what the run time answers
 * rather than against the statement of it.
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
     * How many pieces a split at one code point answers, read off the number the library gives
     * for it: every string of the alphabet, with each of a separator in the basic plane, one
     * outside it and one that is whitespace — so the empty pieces at either end and between two
     * separators are counted, and a code point of two UTF-16 units is counted once.
     */
    @Test
    void howManyPiecesThereAreIsOneMoreThanTheTimesTheSeparatorStands() {
        BoundOperationFacts.Pieces parted = DefaultBoundOperationFacts.get()
                .piecesOf(ValueName.Stdlib.operation("String", "split"));
        for (String separator : List.of(",", "😀", " ")) {
            LinearForm<LawNumber<DeclaredArgument>> howMany =
                    parted.howManyPartedAt(separator.codePointAt(0));
            for (String each : strings()) {
                int pieces = Strings.split(each, separator).size();
                ExactRatio read = valueOf(howMany, each);
                assertEquals(0, ExactRatio.of(pieces).compareTo(read), () -> "of " + show(each)
                        + " at " + show(separator) + ": " + pieces + " pieces, read as "
                        + read.spelled());
            }
        }
    }

    /** What {@code form} comes to where the string split is {@code text}. */
    private static ExactRatio valueOf(LinearForm<LawNumber<DeclaredArgument>> form, String text) {
        List<ExactRatio> terms = new ArrayList<>(List.of(form.constant()));
        for (Map.Entry<LawNumber<DeclaredArgument>, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof LawNumber.CodePointsOf<DeclaredArgument>(
                    LawSubject.Argument<DeclaredArgument> _, CodePointClass counted))) {
                throw new AssertionError("a number of pieces is a count of the string's code"
                        + " points, and this is " + each.getKey());
            }
            long count = text.codePoints().filter(counted::contains).count();
            if (!(each.getValue().times(ExactRatio.of(count))
                    instanceof ExactAnswer.Held<ExactRatio>(ExactRatio term))) {
                throw new AssertionError("a small weight times a small count is held");
            }
            terms.add(term);
        }
        if (!(ExactRatio.sum(terms) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio sum))) {
            throw new AssertionError("a sum of small numbers is held");
        }
        return sum;
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
