package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternMeaning;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
                Language image = StringsOfAPiece.pieceAt(whole, ';', index, MOST_PIECE,
                        ALLOWANCE);
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

    /** Where the walk comes round to the states it began a piece in, a later index is the same. */
    @Test
    void anIndexPastARoundOfTheWalkIsThePieceOfTheIndexInTheRound() {
        Language whole = language("(A;7;)*A");
        Language early = StringsOfAPiece.pieceAt(whole, ';', 3, 1, ALLOWANCE);
        Language late = StringsOfAPiece.pieceAt(whole, ';', 3 + 2 * 1_000_000, 1, ALLOWANCE);
        assertEquals(true, early.has("7") && !early.has("A"));
        assertEquals(true, late.has("7") && !late.has("A"));
    }

    /**
     * A piece is the piece of a string longer than it by the stretches round it. The pieces a
     * language holds of up to a length are the pieces of values only where that length and the
     * stretches come to no more than the longest string, so a caller that cannot say its pieces
     * are short is told nothing, and one that can is told the pieces.
     */
    @Test
    void theLanguageOfPiecesIsAnsweredOnlyForPiecesShortEnoughToBeThoseOfAValue() {
        Language whole = language("A;[A-Z]+");
        assertEquals(null, StringsOfAPiece.pieceAt(whole, ';', 1, Strings.LONGEST_TEXT, ALLOWANCE));
        assertEquals(null, StringsOfAPiece.pieceAt(whole, ';', 1, Strings.LONGEST_TEXT - 1,
                ALLOWANCE));
        Language shortOnes = StringsOfAPiece.pieceAt(whole, ';', 1, 63, ALLOWANCE);
        assertEquals(true, shortOnes.has("ABC") && !shortOnes.has("a"));
    }

    /**
     * The stretches between separators multiply with the index. An index a string of the language
     * reaches within what a String holds is answered, and one it cannot reach is not.
     */
    @Test
    void anIndexIsAnsweredOnlyWhereTheStretchesBeforeItFitInAString() {
        Language whole = language("(AAAAAAAAAA;)*A");
        assertEquals(true, StringsOfAPiece.pieceAt(whole, ';', 15_000_000, 1, ALLOWANCE)
                .has("A"));
        assertEquals(null, StringsOfAPiece.pieceAt(whole, ';', 25_000_000, 1, ALLOWANCE));
    }

    /**
     * A string the language reads as {@code E}, a combining acute and then more is changed by
     * normalization, so it is no value and no value has its piece. The pieces of the values are
     * then not the pieces of the strings, and are not told; where every string is its own
     * normalization they are the same, and are.
     */
    @Test
    void thePiecesOfTheValuesAreToldOnlyWhereNoStringOfTheLanguageIsChangedByNormalization() {
        assertEquals(null, StringsOfAPiece.pieceOfAValueAt(language("A;A|E\\u0301;B"), ';', 1, 1,
                ALLOWANCE));
        Language whole = language("A;[A-C]|D;B");
        assertEquals(StringsOfAPiece.pieceAt(whole, ';', 1, 1, ALLOWANCE),
                StringsOfAPiece.pieceOfAValueAt(whole, ';', 1, 1, ALLOWANCE));
    }

    /** The strings that have a piece are asked of strings a String holds, so no index bounds them
     *  but the machine it takes. */
    @Test
    void anIndexPastWhatTheMeterAllowsAMachineForIsRefused() {
        int past = (int) Strings.LONGEST_TEXT + 1;
        assertEquals(null, StringsOfAPiece.wholesWithAPieceIn(language("A"), ';', past,
                ALLOWANCE));
    }

    /** A machine for an index that the meter's states do not reach is refused unmade. */
    @Test
    void anIndexTheMeterCannotAffordIsRefused() {
        assertEquals(null, StringsOfAPiece.wholesWithAPieceIn(language("A7"), ';', 10,
                new Meter(5, 5, 5)));
    }

    /**
     * What a piece is said to give up of the longest string is no less than what the shortest
     * string of the language with the piece there is longer than the piece by — over every piece of
     * every string of up to eight code points, so a stretch the walk misses on either side of a
     * piece would be a piece standing in a shorter string than the one said.
     */
    @Test
    void thePieceIsShownInAStringNoLongerThanItAndTheStretchesSaidRoundIt() {
        List<String> wholes = everyStringOfUpTo(MOST_WHOLE);
        for (String regex : WHOLES) {
            Language whole = language(regex);
            List<String> held = wholes.stream().filter(whole::has).toList();
            for (int index = 0; index < 4; index++) {
                long around = StringsOfAPiece.mostAround(whole.machine(), ';', index);
                Map<String, Integer> shortest = new HashMap<>();
                for (String each : held) {
                    List<String> parts = Strings.split(each, ";");
                    if (parts.size() > index) {
                        shortest.merge(parts.get(index), each.codePointCount(0, each.length()),
                                Math::min);
                    }
                }
                for (Map.Entry<String, Integer> each : shortest.entrySet()) {
                    long piece = each.getKey().codePointCount(0, each.getKey().length());
                    assertEquals(true, each.getValue() - piece <= around,
                            regex + " at " + index + ": " + each);
                }
            }
        }
    }

    /**
     * An address written round a domain is two code points longer than it, and every domain held
     * as written up to the longest string less those two is shown to be the domain of an address
     * that is a value. A domain an address holds only through a code point normalization changes
     * is a piece of its strings and not shown one of its values, so the two are not told the same.
     */
    @Test
    void aPieceIsShownTheValueOfAStringWrittenRoundIt() {
        Language email = language("[^@\\s]+@[^@\\s]+\\.[^@\\s]+");
        StringsOfAPiece.Shown shown = StringsOfAPiece.piecesOfValuesAt(email, '@', 1, ALLOWANCE);
        assertNotNull(shown);
        assertEquals(Strings.LONGEST_TEXT - 2, shown.upTo());
        assertEquals(true, shown.ofTheValues().has("example.com"));
        assertEquals(false, shown.ofTheStrings().has("example"));
        assertEquals(false, shown.allUpTo(1));

        Language ascii = language("[a-z]+@[a-z]+\\.[a-z]+");
        StringsOfAPiece.Shown written = StringsOfAPiece.piecesOfValuesAt(ascii, '@', 1, ALLOWANCE);
        assertNotNull(written);
        assertEquals(true, written.allUpTo(Strings.LONGEST_TEXT - 2));
        assertEquals(false, written.allUpTo(Strings.LONGEST_TEXT - 1));
    }

    @Test
    void aLanguageWithFewerPiecesThanTheIndexHasNone() {
        assertEquals(true, StringsOfAPiece.pieceAt(language("A7"), ';', 1, 1, ALLOWANCE)
                .isEmpty());
    }
}
