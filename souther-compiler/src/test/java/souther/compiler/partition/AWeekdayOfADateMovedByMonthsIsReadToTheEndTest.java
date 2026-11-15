package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.test.Nightly;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A date moved by months is read in the cases the calendar tells apart, and the cases say which a
 * reading is in without being lines of their own: no row is owed at each month or leap year a
 * move is defined by, and the weekday a first of a month moved by months falls on is read however
 * the first of the month is written and however many moves it is made through.
 *
 * <p>Deferred to the nightly: each of the shapes below is measured in full, which takes about ten
 * seconds a shape, and no cheaper question reads the weekday through the cases of a move. What
 * a change to the reading of a move breaks here is as well found by the morning as by the change.
 * {@code ADateMovedByMonthsIsReadWhereItsDaysAreKnownTest} is what a change waits on.
 */
@Nightly
class AWeekdayOfADateMovedByMonthsIsReadToTheEndTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String MODEL = """
            module demo

            let monthStart (d: Date): Date = Date.addDays(1 - Date.day(d), d)
            let endOfMonth (d: Date): Date =
                Date.addDays(0 - 1, Date.addMonths(1, monthStart(d)))

            behavior f : (x: Date, sunday: Date) -> Bool
            let f (x, sunday) = %s
            """;

    private static final String WEEKDAY = "Int.floorMod(Date.daysBetween(sunday, %s), 7) >= 1";

    /**
     * The shapes that tell the ways a first of a month is read through a move apart: the first of
     * a month that is itself the first of a month moved by months, taken twice, which holds the
     * move of a first and the first of a move in it; and the day before one, which is a move
     * shifted by days.
     */
    private static final List<String> SHAPES = List.of(
            "Date.addMonths(1, monthStart(Date.addMonths(1, monthStart(x))))",
            "endOfMonth(Date.addMonths(1, monthStart(x)))");

    /** The first of a month, moved by months, is read to the end whichever way it is reached. */
    @Test
    void theWeekdayOfAMonthStartMovedByMonthsIsRead() {
        for (String moved : SHAPES) {
            String report = human(WEEKDAY.formatted(moved));
            assertFalse(report.contains("· not read:"), moved + "\n" + report);
            assertTrue(report.contains("measurement: complete"), moved + "\n" + report);
        }
    }

    /** What the date moved is, as cases, draws no line of its own: the lines are the weekday's,
     *  and none is on the month or the year the cases are stated by. */
    @Test
    void theCasesOfAMoveDrawNoLineOfTheirOwn() {
        for (String moved : SHAPES) {
            List<BorderAssessment> lines = Adequacy.readingsOf(
                    measured(WEEKDAY.formatted(moved)).db(), "demo").get("f");
            assertTrue(lines != null && !lines.isEmpty(), moved);
            for (BorderAssessment line : lines) {
                assertTrue(line.left().startsWith("Int.floorMod("), moved + " " + line.left());
            }
        }
    }

    /**
     * A weekday of a date moved by months, whatever day of its month the date is, is taken apart
     * into more cases than a line is taken apart into. It stops there and says so, and the cases
     * of the move are not what it is told for.
     */
    @Test
    void theWeekdayOfAnyDateMovedByMonthsStopsAtTheCasesAndSaysSo() {
        String report = human(WEEKDAY.formatted("Date.addMonths(1, x)"));
        assertTrue(report.contains("CASES_A_LINE_IS_TAKEN_APART_INTO"), report);
        assertFalse(report.contains("a date moved by months"), report);
    }

    private static String human(String comparison) {
        Compilation compilation = measured(comparison);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String comparison) {
        return ACompiledModel.compiles(MEASURED.computeIfAbsent(MODEL.formatted(comparison),
                source -> {
                    Compilation compilation = Compilation.ofSource(source, "Main");
                    compilation.measure(Adequacy.Asked.fullReport());
                    return compilation;
                }));
    }

    /** And given back when the class is done with them: a fork keeps its JVM. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }
}
