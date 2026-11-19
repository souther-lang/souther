package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.UnreadBesideItsStops;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The weekday a first of a month moved by months falls on is read in the cases the calendar tells
 * apart, and the cases say which a reading is in without being lines of their own: no row is owed
 * at each month or leap year a move is defined by.
 *
 * <p>One date asks every way a first of a month is reached through a move: the last day of the
 * month after the first of the month after {@code x}, written out, is a move of a first, the first
 * of a move, a move of that again, and the day before it.
 */
class ADateMovedByMonthsIsReadWhereItsDaysAreKnownTest {

    private static final String MODEL = """
            module demo

            let monthStart (d: Date): Date = Date.addDays(1 - Date.day(d), d)
            let endOfMonth (d: Date): Date =
                Date.addDays(0 - 1, Date.addMonths(1, monthStart(d)))

            behavior f : (x: Date, sunday: Date) -> Bool
            let f (x, sunday) =
                Int.floorMod(Date.daysBetween(sunday, endOfMonth(Date.addMonths(1, monthStart(x)))),
                    7) >= 1
            """;

    private static Compilation measured;

    @BeforeAll
    static void measure() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        measured = ACompiledModel.compiles(compilation);
    }

    /**
     * The weekday is read to the end. A move by months near either end of the calendar stops a
     * run, and no operation of whole numbers is that move, so where it stops is said of the run
     * and not of how it is read ({@link UnreadBesideItsStops}).
     */
    @Test
    void theWeekdayOfAMonthStartMovedByMonthsIsRead() {
        String report = AdequacyReport.of(measured)
                .humanInEnglish(SourceRendering.namedByIdentity(measured.texts()));
        assertFalse(UnreadBesideItsStops.in(report), report);
        assertTrue(report.contains(UnreadBesideItsStops.STOPS_NOT_ALL_TOLD), report);
    }

    /** What the date moved is, as cases, draws no line of its own: the lines are the weekday's,
     *  and none is on the month or the year the cases are stated by. */
    @Test
    void theCasesOfAMoveDrawNoLineOfTheirOwn() {
        List<BorderAssessment> lines = Adequacy.readingsOf(measured.db(), "demo").get("f");
        assertTrue(lines != null && !lines.isEmpty(), String.valueOf(lines));
        for (BorderAssessment line : lines) {
            assertTrue(line.left().startsWith("Int.floorMod("), line.left());
        }
    }

    /** And given back when the class is done with it: a fork keeps its JVM. */
    @AfterAll
    static void released() {
        measured = null;
    }
}
