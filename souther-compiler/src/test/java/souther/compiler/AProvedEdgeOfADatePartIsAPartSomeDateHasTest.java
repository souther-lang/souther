package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point on a day the report proves a row can be written at is a day some date the declarations
 * leave has.
 *
 * <p>The truth is the calendar: the days a February has, over every year, which are the first to
 * the twenty-ninth. A point the report proves is held to it, and a point a date of no declared
 * rule has is held to still be proved, so that what was proved before stays.
 */
class AProvedEdgeOfADatePartIsAPartSomeDateHasTest {

    private static final Pattern RANGE =
            Pattern.compile("^(\\d+) (<|<=) Date\\.\\w+\\(d\\) (<|<=) (\\d+)$");

    /** A part of a date written as a number, or as the run between two. */
    private static final Pattern POINT =
            Pattern.compile("^(\\d+|\\d+ <=? Date\\.\\w+\\(d\\) <=? \\d+)$");

    private static final String BODY = """

            data Out = Int

            behavior go : (d: Day) -> Out
            let go (d) = Out { value = if Date.day(d.value) >= 30 then 1
                                       else (if Date.day(d.value) >= 29 then 2 else 3) }
            """;

    /** The days a date of the model has: a February has the first to the twenty-ninth, which
     *  four years, one of them a leap year, show. */
    private static boolean someFebruaryHas(int day) {
        for (int year = 2000; year < 2004; year++) {
            if (day >= 1 && day <= LocalDate.of(year, 2, 1).lengthOfMonth()) {
                return true;
            }
        }
        return false;
    }

    @Test
    void everyDayProvedForAFebruaryIsADayAFebruaryHas() throws Exception {
        List<String> proved = provedPoints("""
                module demo

                data Day = Date
                    invariant Date.month(value) == 2
                """ + BODY);
        for (String each : proved) {
            assertTrue(someFebruaryDayIn(each), "proved at " + each + ", which no February has");
        }
        assertTrue(proved.contains("29"), proved::toString);
    }

    @Test
    void aDateNoRuleHoldsKeepsTheDaysProvedForIt() throws Exception {
        List<String> proved = provedPoints("""
                module demo

                data Day = Date
                """ + BODY);
        assertEquals(List.of("30", "29", "30 < Date.day(d) <= 31"), proved);
    }

    /** The days a run's date, a day on, is at: a February a day on is never the thirtieth. */
    @Test
    void aDayADateComesToOnceMovedIsProvedOnlyWhereSomeDateComesToIt() throws Exception {
        String body = """

                data Out = Int

                behavior go : (d: Day) -> Out
                let go (d) = Out { value = if Date.day(Date.addDays(1, d.value)) >= 31
                                           then 1 else 2 }
                """;
        List<String> february = provedAt("""
                module demo

                data Day = Date
                    invariant Date.month(value) == 2
                """ + body);
        assertFalse(february.contains("31") || february.contains("30"), february::toString);
        List<String> anyDate = provedAt("""
                module demo

                data Day = Date
                """ + body);
        assertTrue(anyDate.containsAll(List.of("31", "30")), anyDate::toString);
    }

    /** The months the dates {@code holds} leaves come to, moved {@code movedBy} days on, worked
     *  out of the rule as written over four years, one of them a leap year: a rule of the month
     *  and the day turns on the year only at the twenty-ninth of February. */
    private static Set<Integer> monthsOf(Predicate<LocalDate> holds, int movedBy) {
        Set<Integer> out = new TreeSet<>();
        for (LocalDate date = LocalDate.of(2000, 1, 1); date.getYear() < 2004;
                date = date.plusDays(1)) {
            if (holds.test(date)) {
                out.add(date.plusDays(movedBy).getMonthValue());
            }
        }
        return out;
    }

    /** {@code Date.day(value) - Date.month(value) >= 28}. */
    private static boolean twentyEightDaysPastTheMonth(LocalDate date) {
        return date.getDayOfMonth() - date.getMonthValue() >= 28;
    }

    /** The rule leaves the months up to March, and a February would need its thirtieth. */
    private static final String TWENTY_EIGHT_DAYS_PAST_THE_MONTH = """
            module demo

            data Day = Date
                invariant Date.day(value) - Date.month(value) >= 28
            """;

    /** February is between the months the rule leaves, and no date of it holds the rule: one line
     *  at March has March on it and February beside it, and only March is proved. */
    @Test
    void aMonthARuleOfTwoPartsRulesOutIsNotProved() throws Exception {
        Set<Integer> held = monthsOf(
                AProvedEdgeOfADatePartIsAPartSomeDateHasTest::twentyEightDaysPastTheMonth, 0);
        Points points = pointsOf(TWENTY_EIGHT_DAYS_PAST_THE_MONTH + """

                data Out = Int

                behavior go : (d: Day) -> Out
                let go (d) = Out { value = if Date.month(d.value) >= 3 then 1 else 2 }
                """);
        provesOnly(points, held, "2");
        assertTrue(points.proved().contains("3"), points::toString);
    }

    /** The same rule, the date a day on: the thirty-first of January is the first of February,
     *  and no date of the rule is in March a day on. */
    @Test
    void aMonthARuleOfTwoPartsRulesOutOnceMovedIsNotProved() throws Exception {
        Set<Integer> held = monthsOf(
                AProvedEdgeOfADatePartIsAPartSomeDateHasTest::twentyEightDaysPastTheMonth, 1);
        Points points = pointsOf(TWENTY_EIGHT_DAYS_PAST_THE_MONTH + """

                data Out = Int

                behavior go : (d: Day) -> Out
                let go (d) = Out { value = if Date.month(Date.addDays(1, d.value)) >= 3 then 1
                                           else 2 }
                """);
        provesOnly(points, held, "3");
        assertTrue(points.proved().contains("2"), points::toString);
    }

    /** The values of {@code part} the dates {@code holds} leaves come to, over four years as
     *  {@link #monthsOf} reads them. */
    private static Set<Integer> valuesOf(Predicate<LocalDate> holds,
                                         Function<LocalDate, Integer> part) {
        Set<Integer> out = new TreeSet<>();
        for (LocalDate date = LocalDate.of(2000, 1, 1); date.getYear() < 2004;
                date = date.plusDays(1)) {
            if (holds.test(date)) {
                out.add(part.apply(date));
            }
        }
        return out;
    }

    /** A rule of the date a day on: the dates of it are the last day of January and the days of
     *  February but its last, and none of them is in March. */
    @Test
    void aMonthARuleOfAMovedPartRulesOutIsNotProved() throws Exception {
        Set<Integer> held = valuesOf(date -> date.plusDays(1).getMonthValue() == 2,
                LocalDate::getMonthValue);
        provesOnly(pointsOf("""
                module demo

                data Day = Date
                    invariant Date.month(Date.addDays(1, value)) == 2

                data Out = Int

                behavior go : (d: Day) -> Out
                let go (d) = Out { value = if Date.month(d.value) >= 3 then 1 else 2 }
                """), held, "3");
    }

    /** A part of the date moved, held to another field: the dates a day before a January are the
     *  last of December and the days of January but its last, and none of them is in March. */
    @Test
    void aMonthARuleTyingAMovedPartToAnotherPlaceRulesOutIsNotProved() throws Exception {
        Set<Integer> held = valuesOf(date -> date.plusDays(1).getMonthValue() <= 1,
                LocalDate::getMonthValue);
        provesOnly(pointsOf("""
                module demo

                data Span = { start: Date, n: Int }
                    invariant early = Date.month(Date.addDays(1, start)) <= n
                    invariant one = n <= 1

                data Out = Int

                behavior go : (s: Span) -> Out
                let go (s) = Out { value = if Date.month(s.start) >= 3 then 1 else 2 }
                """), held, "3");
    }

    /** The date held by its own ends to the last days of February 2020 and the first of March:
     *  the fifteenth and the fourteenth are days every month has, and no date of the ends. */
    @Test
    void aDayTheEndsOfTheDateRuleOutIsNotProved() throws Exception {
        Set<Integer> held = new TreeSet<>();
        for (LocalDate date = LocalDate.of(2020, 2, 27); !date.isAfter(LocalDate.of(2020, 3, 2));
                date = date.plusDays(1)) {
            held.add(date.getDayOfMonth());
        }
        provesOnly(pointsOf("""
                module demo

                data Day = Date
                    invariant value >= Date("2020-02-27") && value <= Date("2020-03-02")

                data Out = Int

                behavior go : (d: Day) -> Out
                let go (d) = Out { value = if Date.day(d.value) >= 15 then 1 else 2 }
                """), held, "15", "14");
    }

    /** A choice of two days: the tenth and the ninth are days the calendar has, and no date of
     *  the rule has either. */
    @Test
    void aDayAChoiceOfDaysRulesOutIsNotProved() throws Exception {
        Set<Integer> held = valuesOf(date -> date.getDayOfMonth() == 1
                || date.getDayOfMonth() == 15, LocalDate::getDayOfMonth);
        provesOnly(pointsOf("""
                module demo

                data Day = Date
                    invariant Date.day(value) == 1 || Date.day(value) == 15

                data Out = Int

                behavior go : (d: Day) -> Out
                let go (d) = Out { value = if Date.day(d.value) >= 10 then 1 else 2 }
                """), held, "10", "9");
    }

    /** The report of {@code model} with no rows measured: a point is proved writable by what the
     *  model itself says, which is derived whatever is measured. */
    private static JsonNode reportOf(String model) throws Exception {
        Compilation compilation = ACompiledModel.measured(model,
                Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        return JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
    }

    /** What the report proves writable, by the number or run it is at. */
    private static List<String> provedAt(String model) throws Exception {
        JsonNode report = reportOf(model);
        List<String> out = new ArrayList<>();
        for (JsonNode each : report.findParents("knownWritable")) {
            if (each.get("knownWritable").asBoolean() && each.toString().contains("it_is_proved")
                    && each.path("against").isString()) {
                out.add(each.path("against").asString());
            }
        }
        return out;
    }

    /** The points proved writable on a part of a date, as the report writes the number they are
     *  at. */
    private static List<String> provedPoints(String model) throws Exception {
        return pointsOf(model).proved();
    }

    /**
     * The points the report says something of on a part of a date, and those of them it proves
     * writable, by the number or run each is at.
     *
     * @param shown  every point the report holds whether a row can be written at
     * @param proved those of them the rules prove one can, in the order the report holds them
     */
    private record Points(Set<String> shown, List<String> proved) {

        /** Whether the report holds {@code at} and does not prove it. */
        boolean shownAndNotProved(String at) {
            return shown.contains(at) && !proved.contains(at);
        }
    }

    private static Points pointsOf(String model) throws Exception {
        JsonNode report = reportOf(model);
        Set<String> shown = new TreeSet<>();
        List<String> proved = new ArrayList<>();
        for (JsonNode each : report.findParents("knownWritable")) {
            JsonNode against = each.path("against");
            if (!against.isString() || !POINT.matcher(against.asString()).matches()) {
                continue;
            }
            shown.add(against.asString());
            if (each.get("knownWritable").asBoolean() && each.toString().contains("it_is_proved")) {
                proved.add(against.asString());
            }
        }
        return new Points(shown, proved);
    }

    /** Every point proved is a number of {@code held}, and each of {@code unproved} is in the
     *  report and not proved. */
    private static void provesOnly(Points points, Set<Integer> held, String... unproved) {
        for (String each : points.proved()) {
            assertTrue(someNumberIn(each, held), () -> "proved at " + each + ", which none has");
        }
        for (String each : unproved) {
            assertTrue(points.shownAndNotProved(each), () -> each + " in " + points);
        }
    }

    /** Whether some day of a February is among the days {@code written} says, a day or a run. */
    private static boolean someFebruaryDayIn(String written) {
        Set<Integer> february = new TreeSet<>();
        for (int day = 1; day <= 31; day++) {
            if (someFebruaryHas(day)) {
                february.add(day);
            }
        }
        return someNumberIn(written, february);
    }

    /** Whether one of {@code numbers} is among those {@code written} says, a number or a run. */
    private static boolean someNumberIn(String written, Set<Integer> numbers) {
        Matcher run = RANGE.matcher(written);
        int low;
        int high;
        if (run.matches()) {
            low = Integer.parseInt(run.group(1)) + (run.group(2).equals("<") ? 1 : 0);
            high = Integer.parseInt(run.group(4)) - (run.group(3).equals("<") ? 1 : 0);
        } else {
            low = Integer.parseInt(written);
            high = low;
        }
        for (int day = low; day <= high; day++) {
            if (numbers.contains(day)) {
                return true;
            }
        }
        return false;
    }
}
