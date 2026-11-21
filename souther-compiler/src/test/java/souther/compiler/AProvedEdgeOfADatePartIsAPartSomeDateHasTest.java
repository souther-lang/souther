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
        List<String> proved = provedPoints(TWENTY_EIGHT_DAYS_PAST_THE_MONTH + """

                data Out = Int

                behavior go : (d: Day) -> Out
                let go (d) = Out { value = if Date.month(d.value) >= 3 then 1 else 2 }
                """);
        for (String each : proved) {
            assertTrue(someNumberIn(each, held), "proved at " + each + ", which no Day has");
        }
        assertTrue(proved.contains("3"), proved::toString);
    }

    /** The same rule, the date a day on: the thirty-first of January is the first of February,
     *  and no date of the rule is in March a day on. */
    @Test
    void aMonthARuleOfTwoPartsRulesOutOnceMovedIsNotProved() throws Exception {
        Set<Integer> held = monthsOf(
                AProvedEdgeOfADatePartIsAPartSomeDateHasTest::twentyEightDaysPastTheMonth, 1);
        List<String> proved = provedPoints(TWENTY_EIGHT_DAYS_PAST_THE_MONTH + """

                data Out = Int

                behavior go : (d: Day) -> Out
                let go (d) = Out { value = if Date.month(Date.addDays(1, d.value)) >= 3 then 1
                                           else 2 }
                """);
        for (String each : proved) {
            assertTrue(someNumberIn(each, held),
                    "proved at " + each + ", which no Day a day on has");
        }
        assertTrue(proved.contains("2"), proved::toString);
    }

    /** The report of {@code model}, measured as far as what the rules say without running
     *  anything, which is where a point is proved writable: what the arms took is not asked. */
    private static JsonNode reportOf(String model) throws Exception {
        Compilation compilation = ACompiledModel.measured(model,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
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
        JsonNode report = reportOf(model);
        List<String> out = new ArrayList<>();
        for (JsonNode each : report.findParents("knownWritable")) {
            JsonNode against = each.path("against");
            if (each.get("knownWritable").asBoolean() && each.toString().contains("it_is_proved")
                    && against.isString() && POINT.matcher(against.asString()).matches()) {
                out.add(against.asString());
            }
        }
        return out;
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
