package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two numbers taken of places are read by how far apart they are only where the ends of what
 * they take are where the representation stops. Where an end is a line of the operation — a month
 * of twelve, a day of thirty-one, a length of nought — a value at it settles the comparison, and
 * the relation does not leave that number undivided.
 */
class AComparisonOfTwoValuesTakenOfAPlaceKeepsTheEndsOfWhatTheOperationGivesTest {

    private static String report(String body) {
        Compilation compilation = Compilation.ofSource("module p\n\n" + body, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertEquals(0, compilation.errors().size(), report);
        return report;
    }

    private static String completeReport(String body) {
        String report = report(body);
        assertTrue(report.contains("measurement: complete"), report);
        return report;
    }

    private static String dividing(String of) {
        return "rather than dividing the values here, about `" + of + "`";
    }

    /** The point at the end of the operation's answers where a value settles the comparison. */
    private static String excludedAt(String of, String end) {
        return "no IN point is owed at " + of + " = " + end;
    }

    /** A month of twelve is later than none, and one of January is earlier than none. */
    @Test
    void aMonthAtAnEndOfTheYearSettlesAComparisonWithAnother() {
        String report = completeReport("""
                behavior f : (a: Date, b: Date) -> Bool
                let f (a, b) = Date.month(a) < Date.month(b)
                """);

        assertFalse(report.contains(dividing("Date.month(a)")), report);
        assertFalse(report.contains(dividing("Date.month(b)")), report);
        assertTrue(report.contains(excludedAt("Date.month(a)", "12")), report);
        assertTrue(report.contains(excludedAt("Date.month(b)", "1")), report);
    }

    /** A day of thirty-one is later than none, and the first of a month is earlier than none. */
    @Test
    void aDayAtAnEndOfTheMonthSettlesAComparisonWithAnother() {
        String report = completeReport("""
                behavior f : (a: Date, b: Date) -> Bool
                let f (a, b) = Date.day(a) < Date.day(b)
                """);

        assertFalse(report.contains(dividing("Date.day(a)")), report);
        assertFalse(report.contains(dividing("Date.day(b)")), report);
        assertTrue(report.contains(excludedAt("Date.day(a)", "31")), report);
        assertTrue(report.contains(excludedAt("Date.day(b)", "1")), report);
    }

    /** A string of no characters is longer than none, so it settles the comparison. */
    @Test
    void aStringOfNoCharactersSettlesAComparisonOfLengths() {
        String report = report("""
                behavior f : (a: String, b: String) -> Bool
                let f (a, b) = String.length(a) > String.length(b)
                """);

        assertFalse(report.contains(dividing("String.length(a)")), report);
        assertTrue(report.contains(excludedAt("String.length(a)", "0")), report);
    }

    /** The ends of a year are where a date can be written, so they settle nothing. */
    @Test
    void theEndsOfAYearAreWhereADateStopsAndSettleNothing() {
        String report = completeReport("""
                behavior f : (a: Date, b: Date) -> Bool
                let f (a, b) = Date.year(a) < Date.year(b)
                """);

        assertTrue(report.contains(dividing("Date.year(a)")), report);
        assertTrue(report.contains(dividing("Date.year(b)")), report);
        assertFalse(report.contains("no IN point is owed at Date.year"), report);
    }
}
