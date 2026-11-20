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
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
            Pattern.compile("^(\\d+) (<|<=) Date\\.day\\(d\\) (<|<=) (\\d+)$");

    /** A day written as a number, or as the run between two. */
    private static final Pattern DAY = Pattern.compile("^(\\d+|\\d+ <=? Date\\.day\\(d\\) <=? \\d+)$");

    private static final String BODY = """

            data Out = Int

            behavior go : (d: Day) -> Out
            let go (d) = Out { value = if Date.day(d.value) >= 30 then 1
                                       else (if Date.day(d.value) >= 29 then 2 else 3) }
            """;

    /** The days a date of the model has: a February has the first to the twenty-ninth. */
    private static boolean someFebruaryHas(int day) {
        for (int year = 2000; year < 2400; year++) {
            if (day >= 1 && day <= LocalDate.of(year, 2, 1).lengthOfMonth()) {
                return true;
            }
        }
        return false;
    }

    @Test
    void everyDayProvedForAFebruaryIsADayAFebruaryHas() throws Exception {
        List<String> proved = provedDays("""
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
        List<String> proved = provedDays("""
                module demo

                data Day = Date
                """ + BODY);
        assertEquals(List.of("30", "29", "30 < Date.day(d) <= 31"), proved);
    }

    /** The points proved writable on a day, as the report writes the day they are at. */
    private static List<String> provedDays(String model) throws Exception {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        JsonNode report = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<String> out = new ArrayList<>();
        for (JsonNode each : report.findParents("knownWritable")) {
            JsonNode against = each.path("against");
            if (each.get("knownWritable").asBoolean() && each.toString().contains("it_is_proved")
                    && against.isString() && DAY.matcher(against.asString()).matches()) {
                out.add(against.asString());
            }
        }
        return out;
    }

    /** Whether some day of a February is among the days {@code written} says, a day or a run. */
    private static boolean someFebruaryDayIn(String written) {
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
            if (someFebruaryHas(day)) {
                return true;
            }
        }
        return false;
    }
}
