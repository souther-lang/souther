package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A date moved by months is read in the cases the calendar tells apart, and the cases say which a
 * reading is in without being lines of their own: no row is owed at each month or leap year a
 * move is defined by, and the weekday a first of a month moved by months falls on is read however
 * the first of the month is written and however many moves it is made through.
 */
class ADateMovedByMonthsIsReadWhereItsDaysAreKnownTest {

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

    /** The first of a month, moved once and twice, and a month's end behind both. */
    @Test
    void theWeekdayOfAMonthStartMovedByMonthsIsRead() {
        for (String moved : List.of("Date.addMonths(1, monthStart(x))",
                "monthStart(Date.addMonths(1, monthStart(x)))",
                "Date.addMonths(1, monthStart(Date.addMonths(1, monthStart(x))))",
                "endOfMonth(Date.addMonths(1, monthStart(x)))")) {
            String report = human(WEEKDAY.formatted(moved));
            assertFalse(report.contains("· not read:"), moved + "\n" + report);
        }
    }

    /** What the date moved is, as cases, draws no line of its own: the lines are the weekday's,
     *  and none is on the month or the year the cases are stated by. */
    @Test
    void theCasesOfAMoveDrawNoLineOfTheirOwn() {
        for (String moved : List.of("Date.addMonths(1, monthStart(x))",
                "endOfMonth(Date.addMonths(1, monthStart(x)))")) {
            List<BorderAssessment> lines = Adequacy.readingsOf(
                    measured(WEEKDAY.formatted(moved)).db(), "demo").get("f");
            assertTrue(lines != null && !lines.isEmpty(), moved);
            for (BorderAssessment line : lines) {
                assertTrue(line.left().startsWith("Int.floorMod("), moved + " " + line.left());
            }
        }
    }

    /** The day of the month a move lands on is a line on the day of the date moved. */
    @Test
    void theDayAMoveLandsOnIsALineOnTheDay() {
        List<BorderAssessment> lines = Adequacy.readingsOf(
                measured("Date.day(Date.addMonths(1, x)) >= 15").db(), "demo").get("f");
        assertEquals(List.of("Date.day(x)"), lines.stream().map(BorderAssessment::left).toList());
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
