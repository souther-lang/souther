package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison against a number each case of a value names is a line in each case, owed its points
 * in that case and nowhere else.
 *
 * <p>{@code month.value <= minimum(term)} is a line at 12 where {@code term} is {@code OneYear} and
 * a line at 24 where it is {@code TwoYear}. A one-year row never meets the second, so 24 is no edge
 * of a run beside the first: every month above 12 is the same side of it for a one-year term. And
 * the comparison holds below each line, as it does below a fixed one, so the IN point is below.
 *
 * <p>Said with the case, because the place and the values do not tell the two apart: both lines
 * are one comparison at one place, and a row in the range of one of them answers for it only in
 * its case.
 */
class AThresholdEachCaseNamesIsOwedInThatCaseTest {

    private static String model(String condition, String twoYears, String rows) {
        return """
                module example.fee

                data Term = OneYear | TwoYear
                data Month = Int
                    invariant value >= 1 && value <= 60
                data Yen = Int

                behavior cancelFee : (term: Term, month: Month) -> Yen
                    constructs Yen

                let cancelFee (term, month) =
                    if %s then Yen(9500) else Yen(0)

                let minimum (term: Term): Int =
                    match term with
                        | OneYear -> 12
                        | TwoYear -> %s

                example cancelFee
                    | "one year, month 12" : (OneYear, Month(12)) -> Yen(9500)
                    | "one year, month 13" : (OneYear, Month(13)) -> Yen(0)
                    | "two years, month 24" : (TwoYear, Month(%s)) -> Yen(9500)
                %s""".formatted(condition, twoYears, twoYears, rows);
    }

    private static final String WITHIN = "month.value <= minimum(term)";

    @Test
    void eachCasesPointsAreSaidInThatCaseOnTheSideTheComparisonHoldsOn() {
        List<String> readings = readingsOf(model(WITHIN, "24", ""));
        assertTrue(readings.contains("IN in 1 <= month < 12 where term is OneYear"),
                () -> "the one-year IN point is below 12: " + readings);
        assertTrue(readings.contains("OUT in 13 < month <= 60 where term is OneYear"),
                () -> "and its OUT point everything above 13: " + readings);
        assertTrue(readings.contains("IN in 1 <= month < 24 where term is TwoYear"),
                () -> "the two-year IN point is below 24: " + readings);
        assertTrue(readings.contains("OUT in 25 < month <= 60 where term is TwoYear"),
                () -> "and its OUT point everything above 25: " + readings);
    }

    /** Where another case's line is drawn says nothing about where this case's points are. */
    @Test
    void anotherCasesThresholdMovesNoneOfThisCasesPoints() {
        List<String> at24 = oneYearsOf(readingsOf(model(WITHIN, "24", "")));
        List<String> at30 = oneYearsOf(readingsOf(model(WITHIN, "30", "")));
        assertFalse(at24.isEmpty());
        assertEquals(at24, at30);
    }

    /**
     * A one-year row above 24 stands at the one-year OUT point, and a two-year row below 24 is no
     * row at the one-year IN point though its month is in that range.
     */
    @Test
    void aRowAnswersForAPointOnlyInThatPointsCase() {
        String far = "    | \"one year, month 30\" : (OneYear, Month(30)) -> Yen(0)\n";
        List<String> withFar = readingsOf(model(WITHIN, "24", far));
        assertFalse(withFar.contains("OUT in 13 < month <= 60 where term is OneYear"),
                withFar::toString);
        assertTrue(withFar.contains("IN in 1 <= month < 12 where term is OneYear"),
                withFar::toString);
        String other = "    | \"two years, month 5\" : (TwoYear, Month(5)) -> Yen(9500)\n";
        List<String> readings = readingsOf(model(WITHIN, "24", other));
        assertTrue(readings.contains("IN in 1 <= month < 12 where term is OneYear"),
                () -> "a two-year row is no one-year row: " + readings);
        assertFalse(readings.contains("IN in 1 <= month < 24 where term is TwoYear"), () ->
                "and is a two-year one: " + readings);
    }

    /**
     * Written the other way round, or with each case's comparison in an arm of its own, the points
     * are the same: which way round a comparison is spelled is no part of which side it holds on,
     * and a line no row at this one meets bounds none of its runs whichever way it was drawn.
     */
    @Test
    void theSameRuleSpelledOtherwiseIsOwedTheSamePoints() {
        List<String> turned = readingsOf(model("minimum(term) >= month.value", "24", ""));
        assertEquals(readingsOf(model(WITHIN, "24", "")), turned);
        List<String> inArms = readingsOf(model("(match term with | OneYear -> month.value <= 12"
                + " | TwoYear -> month.value <= 24)", "24", ""));
        assertTrue(inArms.contains("IN in 1 <= month < 12"), inArms::toString);
        assertTrue(inArms.contains("OUT in 13 < month <= 60"), inArms::toString);
    }

    /**
     * Two lines a row can meet together still part each other's runs: two comparisons in one arm,
     * and two whose ways overlap without one holding the other. Only a line no row at this one
     * meets is left out.
     */
    @Test
    void aLineARowCanMeetAsWellStillPartsTheRuns() {
        List<String> oneArm = readingsOf(model("(match term with | OneYear -> month.value <= 3"
                + " || (month.value > 6 && month.value <= 12) | TwoYear -> month.value <= 24)",
                "24", ""));
        assertTrue(oneArm.contains("IN in 6 < month < 12"),
                () -> "the line at six bounds the run below the line at twelve: " + oneArm);
        String overlapping = """
                module example.fee

                data Term = OneYear | TwoYear
                data Month = Int
                    invariant value >= 1 && value <= 60
                data Yen = Int

                behavior cancelFee : (term: Term, late: Bool, month: Month) -> Yen
                    constructs Yen

                let cancelFee (term, late, month) =
                    if (match term with | OneYear -> month.value <= 12 | TwoYear -> false)
                        then Yen(9500)
                    else if late && month.value <= 30 then Yen(100)
                    else Yen(0)

                example cancelFee
                    | "one year, month 1" : (OneYear, false, Month(1)) -> Yen(9500)
                """;
        List<String> readings = readingsOf(overlapping);
        assertTrue(readings.contains("OUT in 13 < month <= 30"),
                () -> "a late one-year row meets both, so thirty bounds the run past twelve: "
                        + readings);
    }

    /** Against a fixed number, the IN point of a comparison read as several lines is below the
     *  number, as it is of the comparison alone. */
    @Test
    void aComparisonOfSeveralLinesHoldsBelowItsNumberAsOneLineDoes() {
        List<String> alone = readingsOf(model("month.value <= 12", "24", ""));
        assertEquals(List.of("IN in 1 <= month < 12"), alone);
        assertEquals(alone, readingsOf(model("Int.max(month.value, 3) <= 12", "24", "")));
        List<String> above = readingsOf(model("month.value >= 13", "24", ""));
        assertEquals(above, readingsOf(model("Int.max(month.value, 3) >= 13", "24", "")),
                "and above it, written the other way round");
    }

    /**
     * How many cases there are says nothing about one case's points, whether or not the statement
     * is small enough to be read part against part: a line and a case for each of eight terms is
     * past that, and two terms are well inside it.
     */
    @Test
    void howManyCasesThereAreMovesNoneOfOneCasesPoints() {
        List<String> two = readingsOf(ofTerms(2));
        assertTrue(firstTermsOf(two).containsAll(List.of("IN in 1 <= month < 12 where term is T0",
                "OUT in 13 < month <= 60 where term is T0")), two::toString);
        for (int terms = 3; terms <= 8; terms++) {
            List<String> readings = readingsOf(ofTerms(terms));
            assertEquals(firstTermsOf(two), firstTermsOf(readings), readings::toString);
        }
    }

    /**
     * Past the number of parts a statement is read part against part in, with more cases than
     * that alone: another case's threshold moved moves none of the first case's points.
     */
    @Test
    void anotherCasesThresholdMovesNothingPastTheLimitEither() {
        List<String> before = firstTermsOf(readingsOf(ofTerms(14)));
        assertTrue(before.contains("IN in 1 <= month < 12 where term is T0"), before::toString);
        String moved = ofTerms(14).replace("| T13 -> 90", "| T13 -> 59");
        assertFalse(moved.equals(ofTerms(14)), "the last term's threshold was moved");
        assertEquals(before, firstTermsOf(readingsOf(moved)));
    }

    /**
     * A line is left out of another's runs only where no row is proved to meet both. Two ways
     * this compiler cannot read against each other — a text starting one way and another — are
     * apart for every row, and nothing here shows it, so the second line still bounds the first.
     */
    @Test
    void aLineNothingShowsApartStillPartsTheRuns() {
        String source = """
                module example.fee

                data Month = Int
                    invariant value >= 1 && value <= 60
                data Yen = Int

                behavior cancelFee : (code: String, month: Month) -> Yen
                    constructs Yen

                let cancelFee (code, month) =
                    if String.startsWith("A", code) && month.value <= 12 then Yen(9500)
                    else if String.startsWith("B", code) && month.value <= 24 then Yen(100)
                    else Yen(0)

                example cancelFee
                    | "a, month 1" : ("A", Month(1)) -> Yen(9500)
                """;
        List<String> readings = readingsOf(source);
        assertTrue(readings.stream().anyMatch(each -> each.contains(" in 13 < month <= 24")),
                () -> "the line at 24 bounds the run past 12: " + readings);
    }

    private static List<String> firstTermsOf(List<String> readings) {
        return readings.stream().filter(each -> each.endsWith("where term is T0")).toList();
    }

    /** The minimum of a term of {@code count} cases, twelve months and six more for each. */
    private static String ofTerms(int count) {
        StringBuilder terms = new StringBuilder();
        StringBuilder arms = new StringBuilder();
        for (int i = 0; i < count; i++) {
            terms.append(i == 0 ? "" : " | ").append("T").append(i);
            arms.append("        | T").append(i).append(" -> ").append(12 + 6 * i).append("\n");
        }
        return """
                module example.fee

                data Term = %s
                data Month = Int
                    invariant value >= 1 && value <= 60
                data Yen = Int

                behavior cancelFee : (term: Term, month: Month) -> Yen
                    constructs Yen

                let cancelFee (term, month) =
                    if month.value <= minimum(term) then Yen(9500) else Yen(0)

                let minimum (term: Term): Int =
                    match term with
                %s
                example cancelFee
                    | "first, month 12" : (T0, Month(12)) -> Yen(9500)
                """.formatted(terms, arms);
    }

    private static List<String> oneYearsOf(List<String> readings) {
        return readings.stream().filter(each -> each.endsWith("where term is OneYear")).toList();
    }

    /**
     * What the report asks a row at each reading of a point no row is at to do, after which of the
     * four the point is.
     */
    private static List<String> readingsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String human = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        Pattern point = Pattern.compile("no row is at (?:an|the) (IN|OUT|ON|OFF) point");
        String prefix = "· read as cancelFee/month: ";
        List<String> out = new ArrayList<>();
        String role = null;
        for (String line : human.lines().map(String::strip).toList()) {
            Matcher named = point.matcher(line);
            if (named.find()) {
                role = named.group(1);
            } else if (line.startsWith(prefix)) {
                out.add(role + " " + line.substring(prefix.length()));
            }
        }
        return out;
    }
}
