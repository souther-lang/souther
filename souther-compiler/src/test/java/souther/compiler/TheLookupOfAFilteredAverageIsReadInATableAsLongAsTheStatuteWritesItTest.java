package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.test.Nightly;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.TheLookupOfAFilteredAverageIsReadInATableOfAnyLengthTest.ABOVE_THE_BOUND;
import static souther.compiler.TheLookupOfAFilteredAverageIsReadInATableOfAnyLengthTest.atTheMonths;
import static souther.compiler.TheLookupOfAFilteredAverageIsReadInATableOfAnyLengthTest.unread;

/**
 * The lookup of a filtered average is read in a table of fifty rows, which is as long as the table
 * the statute writes for a grade of remuneration.
 *
 * <p>Nightly, for what it costs: a table that long is most of half a minute of reading, and a
 * table of thirteen rows asks the question of the sharing as well as this does
 * ({@link TheLookupOfAFilteredAverageIsReadInATableOfAnyLengthTest}). This asks that what is
 * shared costs no more than a few readings of one condition for each row, so that the rows the
 * statute has fit in what one condition may read.
 */
@Nightly
class TheLookupOfAFilteredAverageIsReadInATableAsLongAsTheStatuteWritesItTest {

    @Test
    void aTableOfFiftyRowsGivesUpNoRuleAboutTheMonths() {
        assertEquals(List.of(), atTheMonths(unread(50, ABOVE_THE_BOUND)));
    }
}
