package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

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
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String dividing(String of) {
        return "rather than dividing the values here, about `" + of + "`";
    }

    /** A month of twelve is later than none, so it settles the comparison. */
    @Test
    void aMonthAtTheEndOfTheYearSettlesAComparisonWithAnother() {
        String report = report("""
                behavior f : (a: Date, b: Date) -> Bool
                let f (a, b) = Date.month(a) < Date.month(b)
                """);

        assertFalse(report.contains(dividing("Date.month(a)")), report);
        assertFalse(report.contains(dividing("Date.month(b)")), report);
    }

    /** A day of thirty-one is later than none, so it settles the comparison. */
    @Test
    void aDayAtTheEndOfTheMonthSettlesAComparisonWithAnother() {
        String report = report("""
                behavior f : (a: Date, b: Date) -> Bool
                let f (a, b) = Date.day(a) < Date.day(b)
                """);

        assertFalse(report.contains(dividing("Date.day(a)")), report);
        assertFalse(report.contains(dividing("Date.day(b)")), report);
    }

    /** A string of no characters is longer than none, so it settles the comparison. */
    @Test
    void aStringOfNoCharactersSettlesAComparisonOfLengths() {
        String report = report("""
                behavior f : (a: String, b: String) -> Bool
                let f (a, b) = String.length(a) > String.length(b)
                """);

        assertFalse(report.contains(dividing("String.length(a)")), report);
        assertFalse(report.contains(dividing("String.length(b)")), report);
    }

    /** The ends of a year are where a date can be written, so they settle nothing. */
    @Test
    void theEndsOfAYearAreWhereADateStopsAndSettleNothing() {
        String report = report("""
                behavior f : (a: Date, b: Date) -> Bool
                let f (a, b) = Date.year(a) < Date.year(b)
                """);

        assertTrue(report.contains(dividing("Date.year(a)")), report);
        assertTrue(report.contains(dividing("Date.year(b)")), report);
    }
}
