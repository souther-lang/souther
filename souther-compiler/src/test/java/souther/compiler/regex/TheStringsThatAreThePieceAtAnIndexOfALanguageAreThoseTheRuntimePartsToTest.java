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
 * A string is the piece at an index of some string of a language exactly when the runtime's own
 * {@code split} of some string of that language has it there, and a string has a piece at an
 * index in a language exactly when the runtime's {@code split} of it has one there.
 *
 * <p>Held over every string of up to eight code points of an alphabet that has the separator, a
 * letter and a digit, as the whole strings, and every string of up to three as the piece, which
 * holds the empty pieces and the separators side by side and at either end that no list of
 * examples reaches. The languages are ones whose pieces have short strings to show them by.
 */
class TheStringsThatAreThePieceAtAnIndexOfALanguageAreThoseTheRuntimePartsToTest {

    private static final String ALPHABET = "A7;";

    private static final int MOST_WHOLE = 8;

    private static final int MOST_PIECE = 3;

    private static final List<String> WHOLES = List.of("A7;7A", "[A7]+;A*", ".*;[A-Z]7?",
            "A?;A?;A?", "[A-Z]*;7+", "A;7;A;7", "[^;]+;[^;]+;[^;]+", "(A;)?7");

    private static final List<String> PIECES = List.of("[A-Z][0-9]?", "A*", "[A-Z]{2}|[0-9]", ".+",
            "7?A?", "", "A7|7A");

    private static final Meter ALLOWANCE = new Meter(100_000, 10_000_000, 1_000_000_000L);

    private static Language language(String regex) {
        PatternMeaning meaning = assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning();
        Language made = PatternPlan.of(meaning).compile(ALLOWANCE);
        assertNotNull(made, regex);
        return made;
    }

    private static List<String> everyStringOfUpTo(int most) {
        List<String> all = new ArrayList<>(List.of(""));
        List<String> layer = List.of("");
        for (int length = 1; length <= most; length++) {
            List<String> next = new ArrayList<>();
            for (String each : layer) {
                for (int at = 0; at < ALPHABET.length(); at++) {
                    next.add(each + ALPHABET.charAt(at));
                }
            }
            all.addAll(next);
            layer = next;
        }
        return all;
    }

    @Test
    void theyAreTheIndexedPiecesOfTheStringsTheRuntimeParts() {
        List<String> wholes = everyStringOfUpTo(MOST_WHOLE);
        List<String> pieces = everyStringOfUpTo(MOST_PIECE);
        for (String regex : WHOLES) {
            Language whole = language(regex);
            List<String> held = wholes.stream().filter(whole::has).toList();
            for (int index = 0; index < 4; index++) {
                Language image = StringsOfAPiece.pieceAt(whole, ';', index, ALLOWANCE);
                assertNotNull(image, regex + " at " + index);
                for (String piece : pieces) {
                    int at = index;
                    boolean shown = held.stream().anyMatch(text -> {
                        List<String> parts = Strings.split(text, ";");
                        return parts.size() > at && parts.get(at).equals(piece);
                    });
                    assertEquals(shown, image.has(piece),
                            () -> "\"" + piece + "\" as piece " + at + " of " + regex);
                }
            }
        }
    }

    @Test
    void theStringsWithAPieceInALanguageAtAnIndexAreThoseTheRuntimePartsTo() {
        List<String> wholes = everyStringOfUpTo(MOST_WHOLE);
        for (String regex : PIECES) {
            Language piece = language(regex);
            for (int index = 0; index < 4; index++) {
                Language having = StringsOfAPiece.wholesWithAPieceIn(piece, ';', index,
                        ALLOWANCE);
                assertNotNull(having, regex + " at " + index);
                for (String text : wholes) {
                    List<String> parts = Strings.split(text, ";");
                    int at = index;
                    assertEquals(parts.size() > at && piece.has(parts.get(at)), having.has(text),
                            () -> "\"" + text + "\" has piece " + at + " in " + regex);
                }
            }
        }
    }

    @Test
    void aLanguageWithFewerPiecesThanTheIndexHasNone() {
        assertEquals(true, StringsOfAPiece.pieceAt(language("A7"), ';', 1, ALLOWANCE).isEmpty());
    }
}
