package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A relation between two values is said to leave a place undivided only where the other side is
 * shown to stand at every value the relation needs it at, beside every value the place may hold.
 *
 * <p>Each model below is one relation, and what is asked is the word the report gives each place
 * it relates. Three things are shown apart and none of them stands in for another: that the other
 * side takes every value of a run (an unrestricted value, or a number taken of one whose operation
 * declares every number it could answer is one some value answers), that its run is every value
 * between the ends and not only where the values lie, and that nothing on the way to the relation
 * ties it to another place.
 */
class ARelationLeavesAPlaceUndividedOnlyWhereTheOtherSideIsShownToReachItTest {

    private static final String RELATES = "relates";

    private static final String NOT_SHOWN = "not shown";

    /** The word each place is left with by the comparison at {@code at}, by its name. */
    private static Map<String, String> left(String inputs, String declarations, String body,
                                            String at) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                %s
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(declarations, inputs, inputs.replaceAll(": [A-Za-z]+", ""), body),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        Map<String, String> out = new LinkedHashMap<>();
        for (String line : report.lines().map(String::strip).toList()) {
            if (!line.contains("comparison@" + at + " ") || !line.contains("about `")) {
                continue;
            }
            if (!line.startsWith("· no line") && !line.startsWith("· not read")) {
                continue;
            }
            String place = line.substring(line.lastIndexOf("about `") + 7, line.length() - 1);
            out.put(place, line.contains("rather than dividing the values here") ? RELATES
                    : line.contains("not shown to reach every value here") ? NOT_SHOWN : line);
        }
        return out;
    }

    @Test
    void aValueHeldToARunReachesWhatLiesInItAndNoMore() {
        assertEquals(Map.of("a", RELATES, "n", NOT_SHOWN),
                left("a: Amount, n: Int", "data Amount = Int invariant value >= 0",
                        "n == a.value", "4:18"));
    }

    @Test
    void aLengthReachesEveryNumberAtOrAboveNoughtAndNothingBelow() {
        assertEquals(Map.of("String.length(s)", RELATES, "n", NOT_SHOWN),
                left("n: Int, s: String", "data Unused = Int", "n == String.length(s)", "4:18"));
        assertEquals(Map.of("n", RELATES, "String.length(s)", NOT_SHOWN),
                left("n: N, s: String", "data N = Int invariant value >= 0",
                        "n.value == String.length(s)", "4:24"));
    }

    /** A string held to two values takes two lengths with a gap between them. */
    @Test
    void aLengthOfAStringARuleHoldsReachesNothingShown() {
        assertEquals(Map.of("String.length(s)", RELATES, "n", NOT_SHOWN),
                left("n: Int, s: S", "data S = String invariant value == \"a\" || value == \"aaa\"",
                        "n == String.length(s.value)", "4:18"));
    }

    /** An hour is one of twenty-four, which a number running past them is not. */
    @Test
    void anHourReachesTheHoursOfADay() {
        assertEquals(Map.of("Time.hour(t)", RELATES, "n", NOT_SHOWN),
                left("n: Int, t: Time", "data Unused = Int", "n == Time.hour(t)", "4:18"));
        assertEquals(Map.of("h", RELATES, "Time.hour(t)", NOT_SHOWN),
                left("h: H, t: Time", "data H = Int invariant value >= 0 && value <= 23",
                        "h.value == Time.hour(t)", "4:24"));
    }

    /** The years a date can be written in stop somewhere, and a number past them is one no date
     *  is in; and a date held to two first days of January is in two years with one between. */
    @Test
    void aYearReachesTheYearsADateCanBeWrittenInAndNoGapARuleLeaves() {
        assertEquals(Map.of("Date.year(d)", RELATES, "y", NOT_SHOWN),
                left("y: Int, d: Date", "data Unused = Int", "y == Date.year(d)", "4:18"));
        assertEquals(Map.of("y", RELATES, "Date.year(d)", NOT_SHOWN),
                left("y: Y, d: Date", "data Y = Int invariant value >= 1 && value <= 9999",
                        "y.value == Date.year(d)", "4:24"));
        assertEquals(Map.of("Date.year(d)", RELATES, "y", NOT_SHOWN),
                left("y: Int, d: D", "data D = Date invariant value == Date(\"2020-01-01\")"
                        + " || value == Date(\"2022-01-01\")", "y == Date.year(d.value)", "4:18"));
    }

    /** A day apart, the last date has no date after it and the first none before: two values of
     *  one type each settle it at an end, which taking the same values does not reach. */
    @Test
    void twoValuesADayApartAreNotShownToReachEachOther() {
        assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                left("a: Date, b: Date", "data Unused = Int", "Date.daysBetween(a, b) == 1",
                        "4:39"));
    }

    @Test
    void twoValuesOfOneDeclaredTypeReachEachOther() {
        assertEquals(Map.of("c", RELATES, "e", RELATES),
                left("c: Code, e: Code",
                        "data Code = String invariant String.matches(\"[A-Z]{2}\", value)",
                        "e.value == c.value", "4:24"));
    }

    /**
     * A guard on one place narrows where it runs and ties it to nothing: the other place still
     * reaches it. What it reaches is the narrowed run, which a value of the other place below it
     * is not on.
     */
    @Test
    void aGuardOnOnePlaceNarrowsItAndTiesItToNothing() {
        assertEquals(Map.of("a", RELATES, "b", NOT_SHOWN),
                left("a: Int, b: Int", "data Unused = Int", "if a > 0 then a < b else false",
                        "4:32"));
    }

    /**
     * What a weighed term has to stand at is the rest over its weight: under {@code 2h + y < 0}
     * with {@code y} at most minus five, {@code y} at minus five needs an {@code h} below two and a
     * half, which an {@code h} from four on never is.
     */
    @Test
    void aWeighedTermHasToStandAtTheRestOverItsWeight() {
        String declarations = "data Y = Int invariant value >= -10 && value <= -5";
        assertEquals(Map.of("h", NOT_SHOWN, "y", NOT_SHOWN),
                left("h: Int, y: Y", declarations,
                        "if h >= 4 && h <= 11 then 2 * h + y.value < 0 else false", "4:58"));
        assertEquals(Map.of("h", NOT_SHOWN, "y", RELATES),
                left("h: Int, y: Y", declarations,
                        "if h >= 0 && h <= 20 then 2 * h + y.value < 0 else false", "4:58"));
    }

    /** A way over two places ties them, however each runs on its own. */
    @Test
    void aWayOverTwoPlacesTiesThem() {
        assertEquals(Map.of("x", NOT_SHOWN, "y", NOT_SHOWN),
                left("x: Int, y: Int", "data Unused = Int",
                        "if x + y <= 1 then x == y else false", "4:37"));
    }

    /** A way over another number of the date a year is taken of ties the year to it: a date on
     *  the twenty-ninth of February is in a leap year. */
    @Test
    void aWayOverAnotherNumberOfTheSamePlaceTiesTheNumberTakenOfIt() {
        assertEquals(List.of(NOT_SHOWN), List.copyOf(left("y: Int, d: Date", "data Unused = Int",
                "if Date.month(d) == 2 && Date.day(d) == 29 then y == Date.year(d) else false",
                "4:66").entrySet().stream()
                .filter(each -> each.getKey().equals("y")).map(Map.Entry::getValue).toList()));
    }
}
