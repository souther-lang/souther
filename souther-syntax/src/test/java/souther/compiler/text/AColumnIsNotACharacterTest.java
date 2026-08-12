package souther.compiler.text;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.IdentifierAlphabet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a text occupies when it is written out, held against the two counts it is not.
 *
 * <p>The counts agree on ASCII and disagree wherever the interesting characters are, so a case
 * that does not carry one of them proves nothing. The emoji below is here for the opposite reason
 * to the rest: it is the case where counting UTF-16 units happens to give the right answer, which
 * is what makes counting code points look like the fix and is why it is written down.
 */
class AColumnIsNotACharacterTest {

    private static final String CJK = "免責金額";
    /** One code point, two UTF-16 units, two columns. */
    private static final String EMOJI = "🎉";

    @Test
    void an_ascii_text_occupies_a_column_per_character() {
        assertEquals(3, DisplayColumns.width("abc"));
        assertEquals(0, DisplayColumns.width(""));
    }

    @Test
    void a_full_width_character_occupies_two_columns() {
        assertEquals(8, DisplayColumns.width(CJK));
        assertEquals(4, CJK.length(), "and four UTF-16 units, which is the count being replaced");
        assertEquals(4, CJK.codePointCount(0, CJK.length()),
                "and four code points, which is the other count it is not");
    }

    /**
     * The negative control. Counting UTF-16 units answers this one correctly and counting code
     * points answers it wrongly, so a change from {@code length()} to {@code codePointCount()}
     * would fail here while leaving every full-width case as it was.
     */
    @Test
    void a_supplementary_character_is_where_the_wrong_counts_swap_places() {
        assertEquals(2, DisplayColumns.width(EMOJI));
        assertEquals(2, EMOJI.length());
        assertNotEquals(DisplayColumns.width(EMOJI), EMOJI.codePointCount(0, EMOJI.length()));
    }

    /** East Asian Width {@code A} is one column. Terminals disagree about it, so the convention
     *  settles it rather than reporting it. */
    @Test
    void an_ambiguous_width_character_occupies_one_column() {
        assertEquals(1, DisplayColumns.width("¡"));
        assertEquals(1, DisplayColumns.width("‘"));
    }

    /**
     * A tab has no width of its own. The same tab measured from four starting columns gives three
     * different answers, which is what a text-only width function cannot say.
     */
    @Test
    void a_tab_advances_to_the_next_stop_and_so_depends_on_where_it_began() {
        assertEquals(8, DisplayColumns.advance("\t", 0));
        assertEquals(8, DisplayColumns.advance("\t", 1));
        assertEquals(8, DisplayColumns.advance("\t", 7));
        assertEquals(16, DisplayColumns.advance("\t", 8));
        assertEquals(16, DisplayColumns.advance("\t", 9));
    }

    @Test
    void a_width_is_an_advance_from_the_start_of_a_line() {
        assertEquals(DisplayColumns.advance("a\tb", 0), DisplayColumns.width("a\tb"));
        assertEquals(9, DisplayColumns.width("a\tb"));
    }

    @Test
    void an_advance_carries_on_from_where_the_last_one_ended() {
        int at = DisplayColumns.advance("let ", 0);
        at = DisplayColumns.advance(CJK, at);
        assertEquals(DisplayColumns.width("let " + CJK), at);
    }

    /** What a format string's own field width cannot do, because it pads inside the formatter and
     *  counts UTF-16 units there. */
    @Test
    void padding_fills_columns_rather_than_characters() {
        assertEquals(10, DisplayColumns.width(DisplayColumns.padRight(CJK, 10)));
        assertEquals(10, DisplayColumns.width(DisplayColumns.padRight("abc", 10)));
        assertEquals(10, DisplayColumns.width(DisplayColumns.padRight(EMOJI, 10)));
        assertEquals(CJK, DisplayColumns.padRight(CJK, 4), "already past the width, so unpadded");
        assertEquals(14, DisplayColumns.width(String.format("%-10s", CJK)),
                "which is what the format string it replaces writes, and why it is replaced");
    }

    /**
     * The whole of what is left out. Nothing composes: a mark is measured on its own rather than
     * folded into the letter it is written over, so a decomposed {@code が} is answered four where
     * the precomposed one is answered two and a terminal draws them alike. Written down because the
     * convention answers for every code point — there is no character it declines — and what it
     * does not model is reading more than one of them at a time.
     */
    @Test
    void nothing_composes_so_a_mark_is_measured_on_its_own() {
        assertEquals(2, DisplayColumns.width("\u304C"), "precomposed \u304C");
        assertEquals(4, DisplayColumns.width("\u304B\u3099"),
                "the same syllable decomposed, answered as its two parts");
        assertEquals(2, DisplayColumns.width("e\u0301"),
                "and a mark that is not wide is still a column of its own");
    }

    /**
     * The two Unicode files are read separately and have to be read at one version. Held against
     * each other rather than against a constant, because a constant would be a third copy of an
     * answer both files already carry.
     */
    @Test
    void the_widths_and_the_alphabet_are_read_at_one_unicode_version() {
        assertEquals(IdentifierAlphabet.unicodeVersion(), DisplayColumns.unicodeVersion());
        assertTrue(DisplayColumns.unicodeVersion().matches("\\d+\\.\\d+\\.\\d+"),
                DisplayColumns.unicodeVersion());
    }
}
