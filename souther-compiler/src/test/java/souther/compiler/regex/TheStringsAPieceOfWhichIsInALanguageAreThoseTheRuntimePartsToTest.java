package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternMeaning;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The strings some piece, or every piece, of a window of which is in a language are the strings
 * the runtime parts into pieces of which some, or every, one of that window is.
 *
 * <p>Held over every string of up to six code points of an alphabet that has the separator, a
 * letter and a digit, which holds the empty pieces, the separators side by side and at either end
 * that no list of examples reaches, against the runtime's own {@code split}.
 */
class TheStringsAPieceOfWhichIsInALanguageAreThoseTheRuntimePartsToTest {

    private static final String ALPHABET = "A7;";

    private static final int MOST_CODE_POINTS = 6;

    private static final List<String> PIECES = List.of("[A-Z][0-9]", "A*", "[A-Z]{2}|[0-9]", ".+",
            "7?A?");

    /** Each window as {@code from} and {@code until}: the whole, the dropped, the taken, and the
     *  two of them in both orders. */
    private static final List<int[]> WINDOWS = List.of(
            new int[] {0, StringsByTheirPieces.TO_THE_LAST},
            new int[] {1, StringsByTheirPieces.TO_THE_LAST},
            new int[] {2, StringsByTheirPieces.TO_THE_LAST},
            new int[] {0, 1},
            new int[] {0, 2},
            new int[] {1, 2},
            new int[] {1, 3},
            new int[] {2, 4});

    private static Language language(PatternMeaning meaning) {
        Language made = PatternPlan.of(meaning).compile(new Meter(100_000, 10_000_000,
                1_000_000_000L));
        assertNotNull(made, meaning.toString());
        return made;
    }

    private static PatternMeaning meaningOf(String regex) {
        return assertInstanceOf(PatternRead.Read.class, PatternParser.read(regex), regex)
                .meaning();
    }

    private static List<String> everyString() {
        List<String> all = new ArrayList<>(List.of(""));
        List<String> layer = List.of("");
        for (int length = 1; length <= MOST_CODE_POINTS; length++) {
            List<String> next = new ArrayList<>();
            for (String each : layer) {
                for (char symbol : ALPHABET.toCharArray()) {
                    next.add(each + symbol);
                }
            }
            all.addAll(next);
            layer = next;
        }
        return all;
    }

    private static List<String> piecesIn(String text, int[] window) {
        List<String> pieces = Strings.split(text, ";");
        int from = Math.min(window[0], pieces.size());
        int until = window[1] == StringsByTheirPieces.TO_THE_LAST ? pieces.size()
                : Math.min(window[1], pieces.size());
        return pieces.subList(from, until);
    }

    @Test
    void someIsWhatTheRuntimePartsInto() {
        List<String> strings = everyString();
        for (String regex : PIECES) {
            Language piece = language(meaningOf(regex));
            for (int[] window : WINDOWS) {
                Language some = language(StringsByTheirPieces.someIn(meaningOf(regex), ';',
                        window[0], window[1]));
                for (String text : strings) {
                    assertEquals(piecesIn(text, window).stream().anyMatch(piece::has),
                            some.has(text),
                            () -> "some piece in " + List.of(window[0], window[1]) + " of \""
                                    + text + "\" in " + regex);
                }
            }
        }
    }

    @Test
    void everyIsWhatTheRuntimePartsInto() {
        List<String> strings = everyString();
        for (String regex : PIECES) {
            Language piece = language(meaningOf(regex));
            for (int[] window : WINDOWS) {
                Language every = language(StringsByTheirPieces.everyIn(meaningOf(regex), ';',
                        window[0], window[1]));
                for (String text : strings) {
                    assertEquals(piecesIn(text, window).stream().allMatch(piece::has),
                            every.has(text),
                            () -> "every piece in " + List.of(window[0], window[1]) + " of \""
                                    + text + "\" in " + regex);
                }
            }
        }
    }
}
