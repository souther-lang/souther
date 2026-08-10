package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body comparing a date draws a line, and the rows are owed both sides of it.
 *
 * <p>{@code Date} is one of the ordered primitives — {@code <} typechecks and the branch is real —
 * and the reading that draws lines was written for numbers, so a rule dividing an input by a date
 * came back as a position the model divides no way. Every business rule with a cutover date is this
 * one.
 *
 * <p>A date is a discrete total order, so what an interval and a neighbour need of it is what a whole
 * number gives: compare, and the value one step either way. Nothing about that is arithmetic on the
 * text, and nothing a row or a report shows may be the count that carries it — an author reads
 * {@code Date("2026-01-01")}, never a day number.
 */
class ALineDrawnOnADateIsALineTest {

    private static final String MODEL = """
            module example.dated

            data Stale
            data Fresh

            behavior freshness : (on: Date) -> Stale | Fresh
                constructs Stale, Fresh
            let freshness (on) = if on < Date("2026-01-01") then Stale else Fresh

            example freshness
                | "before the line" : (Date("2025-12-31")) -> Stale
            """;

    private static String report() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human();
    }

    /** The position is divided, where it used to be one nothing was established about. */
    @Test
    void thePositionIsDivided() {
        String human = report();

        assertTrue(human.contains("partition   axes 1"), human);
        assertFalse(human.contains("not read: on"), human);
    }

    /** Both sides of the line are owed, and the row already written covers the one it is on. */
    @Test
    void bothSidesOfTheLineAreOwed() {
        String human = report();

        assertTrue(human.contains("boundary    1/2"), human);
        assertTrue(human.contains("2026-01-01"), human);
    }

    /** What a report shows is the date, never the count that carries it. */
    @Test
    void nothingShowsTheDayNumber() {
        String human = report();

        assertFalse(human.contains("20454"), human);
        assertFalse(human.contains("20453"), human);
    }
}
