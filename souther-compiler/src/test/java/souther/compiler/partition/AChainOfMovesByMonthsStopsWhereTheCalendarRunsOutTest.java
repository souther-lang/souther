package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A chain of moves by months off the first of a month that stops somewhere in the chain is read
 * as stopping there, whatever the months of the chain come to.
 *
 * <p>The cases a move is read in say the date it lands on and say nothing of where the calendar
 * runs out, so a row that reaches the end is told by running it: the move stops at the call it
 * stopped at, and no row is said to be composed ({@link MonthMovesInCases}). That holds for a
 * chain where it holds for one move: at the end of the calendar, where each move of it is read,
 * and for a move by more months than are read in cases, which a chain of moves that cancel
 * must not read as the one by nought.
 */
class AChainOfMovesByMonthsStopsWhereTheCalendarRunsOutTest {

    private static final String FIRST = "Date.addDays(1 - Date.day(d), d)";

    private static String report(String body) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                behavior f : (d: Date) -> Int
                let f (d) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static void stopsInTheChain(String report) {
        assertTrue(report.contains("months is outside the range it can hold"), report);
        assertTrue(report.contains("no row composed here was run to an answer"), report);
    }

    @Test
    void movesThatCancelButAreByMoreMonthsThanAreReadStopWhereTheFirstDoes() {
        stopsInTheChain(report("Date.day(Date.addMonths(-25000000000,"
                + " Date.addMonths(25000000000, " + FIRST + ")))"));
    }

    @Test
    void aMoveOneWayAndBackStopsAtTheLastMonthTheCalendarHas() {
        stopsInTheChain(report("if Date.year(d) == 999999999 && Date.month(d) == 12 then"
                + " Date.day(Date.addMonths(-1, Date.addMonths(1, " + FIRST + "))) else 0"));
    }

    @Test
    void aMoveTheOtherWayAndBackStopsAtTheFirstMonthTheCalendarHas() {
        stopsInTheChain(report("if Date.year(d) == 0 - 999999999 && Date.month(d) == 1 then"
                + " Date.day(Date.addMonths(1, Date.addMonths(-1, " + FIRST + "))) else 0"));
    }

    @Test
    void aChainInAYearTheCalendarHasMonthsOnEitherSideOfStopsNowhere() {
        assertFalse(report("if Date.year(d) == 2026 then Date.day(Date.addMonths(1,"
                + " Date.addMonths(1, " + FIRST + "))) else 0").contains("outside the range"));
    }
}
