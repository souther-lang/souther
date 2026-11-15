package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A row is composed for each point of the weekday a date falls on, beside a condition on a part of
 * the same date: the weekday is of the date's day count and the day of its month, and a condition
 * on the month or on what the year leaves holds the date to some days, so the numbers chosen for
 * the weekday are of one date that meets the condition.
 *
 * <p>Two conditions, since each is held to the date another way: a month fixed is a part of the
 * date, which the days it holds the date to follow from; a remainder of the year is a class of
 * years, which no run of numbers says and the way the date is reached by carries.
 */
class AWeekdayBesideAConditionOnADatesPartIsBuiltTest {

    private static final String MODEL = """
            module demo

            behavior g : (x: Date, sunday: Date) -> Bool
            let g (x, sunday) = if %s then Int.floorMod(Date.daysBetween(sunday,
                Date.addDays(1 - Date.day(x), x)), 7) >= 1 else false

            example g
                | "a" : (Date("2026-07-20"), Date("2026-01-04")) -> false
            """;

    private static String report(String condition) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(condition), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return AdequacyReport.of(ACompiledModel.compiles(compilation))
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void aMonthFixedBesideTheWeekdayLeavesNoPointUnbuilt() {
        assertFalse(report("Date.month(x) == 2").contains("nothing could show a row can be written"));
    }

    @Test
    void aRemainderOfTheYearBesideTheWeekdayLeavesNoPointUnbuilt() {
        assertFalse(report("Int.floorMod(Date.year(x), 4) == 0")
                .contains("nothing could show a row can be written"));
    }
}
