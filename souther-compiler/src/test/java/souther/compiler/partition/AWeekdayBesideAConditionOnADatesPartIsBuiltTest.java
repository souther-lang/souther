package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.time.LocalDate;
import java.time.temporal.ChronoUnit;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row is composed for each point of the weekday a date falls on, beside a condition on a part of
 * the same date: the weekday is of the date's day count and the day of its month, and a condition
 * on the month or on what the year leaves holds the date to some days, so the numbers chosen for
 * the weekday are of one date that meets the condition.
 *
 * <p>Two conditions, since each is held to the date another way: a month fixed is a part of the
 * date, which the days it holds the date to follow from; a remainder of the year is a class of
 * years, which no run of numbers says and the way the date is reached by carries.
 *
 * <p>What is asked is the rows themselves. A row is composed for every point the rules draw, and
 * what each row's dates come to, worked out here from the dates and not from what the report says,
 * is what its point says and meets the condition that leads to the weekday.
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

    private static final String WEEKDAY = "Int.floorMod(-Date.day(x) - sunday + x + 1, 7)";

    private static Compilation compiled(String condition) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(condition), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The two dates a row is made of: the date asked of and the Sunday its weeks are counted
     *  from. */
    private record Dates(LocalDate x, LocalDate sunday) {

        static Dates of(Generator.GeneratedRow row) {
            List<String> texts = row.inputs().stream().map(each -> each.text()).toList();
            return new Dates(parsed(texts.get(0)), parsed(texts.get(1)));
        }

        private static LocalDate parsed(String text) {
            return LocalDate.parse(text.substring("Date(\"".length(), text.length() - 2));
        }

        /** What the weekday the model computes comes to for these dates. */
        long weekday() {
            LocalDate firstOfTheMonth = x.withDayOfMonth(1);
            return Math.floorMod(ChronoUnit.DAYS.between(sunday, firstOfTheMonth), 7);
        }
    }

    /** The rows composed for the points the rules draw, by the label of the point. */
    private static Map<String, Dates> pointsOf(Compilation compilation) {
        Map<String, Dates> out = new LinkedHashMap<>();
        for (Generator.GeneratedRow row : Adequacy.generatedOf(compilation.db(), "demo").get("g")
                .boundaries().rows()) {
            for (Generator.Purpose purpose : row.purposes()) {
                if (purpose instanceof Generator.Purpose.ForAPoint point) {
                    assertEquals(null, out.put(point.label(), Dates.of(row)),
                            "one row is composed for " + point.label());
                }
            }
        }
        return out;
    }

    /** Each point the weekday draws, and what a date has that is at it. */
    private static final Map<String, Predicate<Dates>> WEEKDAY_POINTS = Map.of(
            WEEKDAY + " = 1", dates -> dates.weekday() == 1,
            WEEKDAY + " = 0", dates -> dates.weekday() == 0,
            "1 < " + WEEKDAY + " <= 6", dates -> dates.weekday() > 1 && dates.weekday() <= 6);

    private static void everyPointIsBuiltAndMeansWhatItSays(
            Compilation compilation, Map<String, Predicate<Dates>> conditionPoints,
            Predicate<Dates> leadsToTheWeekday) {
        String report = report(compilation);
        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("nothing could show a row can be written"), report);
        Map<String, Dates> points = pointsOf(compilation);
        Map<String, Predicate<Dates>> asked = new LinkedHashMap<>(conditionPoints);
        asked.putAll(WEEKDAY_POINTS);
        assertEquals(asked.keySet(), points.keySet(), "a row for each point the rules draw");
        asked.forEach((label, holds) -> assertTrue(holds.test(points.get(label)),
                "the row for " + label + " is of " + points.get(label)));
        WEEKDAY_POINTS.keySet().forEach(label -> assertTrue(
                leadsToTheWeekday.test(points.get(label)),
                "the row for " + label + " reaches the weekday: " + points.get(label)));
    }

    @Test
    void aMonthFixedBesideTheWeekdayBuildsARowForEveryPoint() {
        everyPointIsBuiltAndMeansWhatItSays(compiled("Date.month(x) == 2"),
                Map.of("Date.month(x) = 2", dates -> dates.x().getMonthValue() == 2,
                        "Date.month(x) = 1", dates -> dates.x().getMonthValue() == 1,
                        "Date.month(x) = 3", dates -> dates.x().getMonthValue() == 3),
                dates -> dates.x().getMonthValue() == 2);
    }

    @Test
    void aRemainderOfTheYearBesideTheWeekdayBuildsARowForEveryPoint() {
        everyPointIsBuiltAndMeansWhatItSays(compiled("Int.floorMod(Date.year(x), 4) == 0"),
                Map.of("Int.floorMod(Date.year(x), 4) = 0",
                        dates -> Math.floorMod(dates.x().getYear(), 4) == 0,
                        "Int.floorMod(Date.year(x), 4) = 1",
                        dates -> Math.floorMod(dates.x().getYear(), 4) == 1),
                dates -> Math.floorMod(dates.x().getYear(), 4) == 0);
    }
}
