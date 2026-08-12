package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the formatter measures a construct against, and what it does not.
 *
 * <p>The width is a width on the screen. A layout also carries offsets into the text it wrote, and
 * those are indices into a Java string. Both are integers about the same line and they are not the
 * same number, so the two are held apart here: the first pair of cases would pass with either
 * measure if the measure did not have to be absolute, and the last pair fails if the offsets are
 * moved along with the columns.
 */
class AWidthIsMeasuredInColumnsNotCharactersTest {

    /**
     * The same width left, and a different answer.
     *
     * <p>Both groups are measured with five columns to spare. One begins at column 7 and its tab
     * carries it one column to the next stop; the other begins at column 8 and its tab carries it
     * eight. Nothing about how much of the width is left can tell those apart, which is why a fit
     * is walked forward from where the group stands rather than subtracted from what remains.
     */
    @Test
    void a_fit_is_decided_by_the_column_a_group_stands_at() {
        Doc atSeven = Doc.concat(Doc.text("x".repeat(7)), Doc.group(Doc.text("\tabc")));
        Doc atEight = Doc.concat(Doc.text("x".repeat(8)), Doc.group(Doc.text("\tabc")));

        Outcome fits = atSeven.layout(12).decisions().get(0).outcome();
        Outcome over = atEight.layout(13).decisions().get(0).outcome();

        assertEquals(5, 12 - 7, "five columns to spare");
        assertEquals(5, 13 - 8, "and five columns to spare");
        assertInstanceOf(Outcome.Flat.class, fits, "column 7, so the tab advances one");
        assertInstanceOf(Outcome.BrokenByWidth.class, over, "column 8, so the tab advances eight");
        assertNotEquals(fits, over);
    }

    /** And the column a group is measured from is a column, so a full-width name moves it by two
     *  per character. */
    @Test
    void a_group_is_measured_from_the_column_the_line_has_reached() {
        Doc doc = Doc.concat(Doc.text("免責金額"), Doc.group(Doc.text("ab")));
        assertEquals(8, doc.layout(100).decisions().get(0).startColumn(),
                "four characters, eight columns");
    }

    /**
     * The other half of the contract. Everything a layout says about where something is in its text
     * — a break's offset, a break opportunity's — indexes the text it wrote, and the readers of a
     * layout cut and search that string with it. Moving those to columns alongside the width would
     * leave every one of them pointing into the middle of nothing.
     */
    @Test
    void an_offset_a_layout_reports_still_indexes_its_text() {
        Doc doc = Doc.group(Doc.concat(Doc.text("免責金額"), Doc.line(), Doc.text("ab")));

        Layout flat = doc.layout(100);
        assertEquals("免責金額 ab", flat.text());
        int at = flat.opportunities().get(0).at();
        assertEquals(4, at, "four UTF-16 units, where the columns would have said eight");
        assertEquals(" ab", flat.text().substring(at));

        Layout broken = doc.layout(4);
        assertEquals("免責金額\nab", broken.text());
        int offset = broken.breaks().get(0).offset();
        assertEquals(4, offset);
        assertEquals('\n', broken.text().charAt(offset));
    }

    /**
     * The rule the formatter states, on a construct that fits by one measure and not the other. The
     * record below is 85 UTF-16 units and 139 columns written on one line, so a formatter counting
     * characters writes it whole and then states that its lines are at most 100 columns.
     */
    @Test
    void a_construct_that_fits_in_characters_and_not_in_columns_is_written_down_the_page() {
        String formatted = Formatter.format("""
                module 医療.支払

                data 金額 = Int
                    invariant value >= 0

                data 診療報酬明細 =
                    { 初診料加算額: 金額
                    , 再診料加算額: 金額
                    , 入院基本料額: 金額
                    }

                behavior 明細合算 : (明細: 診療報酬明細) -> 診療報酬明細

                let 明細合算 (明細) =
                    診療報酬明細
                        { 初診料加算額 = 明細.初診料加算額
                        , 再診料加算額 = 明細.再診料加算額
                        , 入院基本料額 = 明細.入院基本料額
                        }
                """);

        for (String line : formatted.split("\n", -1)) {
            assertTrue(columnsOf(line) <= 100, "over the stated width: " + line);
        }
        assertTrue(formatted.lines().anyMatch(l -> l.stripLeading().startsWith("初診料加算額 =")),
                "the record body is written down the page rather than on one line");
    }

    /** An accounting of the columns that does not read the table under test. Every character these
     *  cases use is a CJK ideograph or ASCII, which is all this has to be right about. */
    private static int columnsOf(String text) {
        int at = 0;
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            at += (c >= 0x2E80 && c <= 0xA4CF) || (c >= 0xFF00 && c <= 0xFF60) ? 2 : 1;
        }
        return at;
    }
}
