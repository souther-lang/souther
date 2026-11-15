package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternMeaning;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import souther.runtime.Strings;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A piece is the piece of no value once it is longer than the longest string less the fewest code
 * points that any string of the language has round a piece there. That is the fewest over every
 * way a string stands round the piece, where the most a piece may need round it says how long a
 * piece is shown to be the piece of a value, and nothing of how long one can be.
 */
class ThePiecesNoStringHoldsPastTheStretchRoundThemAreThePieceOfNoValueTest {

    private static final int AT = '@';

    private static Language language(String regex) {
        PatternMeaning meaning = assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning();
        Language made = PatternPlan.of(meaning).compile(new Meter(100_000, 10_000_000,
                1_000_000_000L));
        assertNotNull(made, regex);
        return made;
    }

    private static StringsOfAPiece.Shown shownAtOne(String regex) {
        Meter meter = new Meter(100_000, 10_000_000, 1_000_000_000L);
        return StringsOfAPiece.piecesOfValuesAt(language(regex), AT, 1, meter);
    }

    /**
     * Written round a piece, the long local part takes five code points and the short one two. A
     * piece that fits the short one is a piece of a value up to the longest string less two, though
     * it is shown to be one only up to the longest less five.
     */
    @Test
    void theFewestRoundAPieceIsWhatTheShortestWayOfWritingARoundItTakes() {
        Language whole = language("a@[a-z]+|long@[0-9]+");

        assertEquals(5, StringsOfAPiece.mostAround(whole.machine(), AT, 1));
        assertEquals(2, StringsOfAPiece.leastAround(whole.machine(), AT, 1));

        StringsOfAPiece.Shown shown = shownAtOne("a@[a-z]+|long@[0-9]+");
        assertEquals(Strings.LONGEST_TEXT - 5, shown.upTo());
        assertEquals(Strings.LONGEST_TEXT - 2, shown.noneBeyond());
    }

    /** A string with no piece at the index has none longer than anything: no piece is a value's. */
    @Test
    void aLanguageWithNoPieceAtTheIndexHoldsNoneOfAnyLength() {
        Language whole = language("abc");

        assertEquals(Long.MAX_VALUE, StringsOfAPiece.leastAround(whole.machine(), AT, 1));
        assertEquals(-1, shownAtOne("abc").noneBeyond());
    }

    /** Past the machine's states only the separators before the piece are counted. */
    @Test
    void anIndexPastTheMachinesStatesCountsTheSeparatorsBeforeThePiece() {
        Language whole = language("a@b");

        assertEquals(40, StringsOfAPiece.leastAround(whole.machine(), AT, 40));
    }
}
