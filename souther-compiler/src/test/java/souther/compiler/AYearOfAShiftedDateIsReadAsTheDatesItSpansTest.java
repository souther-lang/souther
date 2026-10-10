package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of the year of a date made from the input is read as the comparison of that date
 * with where the year begins.
 *
 * <p>{@code Date.year(Date.addDays(1, b)) >= 2027} holds where {@code Date.addDays(1, b)} is on or
 * after the first of January 2027, which is where {@code b} is on or after the thirty-first of
 * December before it. The rows below are run, so the lines drawn are held to what the program
 * computes and not to the arithmetic that drew them.
 */
class AYearOfAShiftedDateIsReadAsTheDatesItSpansTest {

    private static String report(String behavior) {
        Compilation compilation = Compilation.ofSource("module m\n\n" + behavior, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String about(String comparison) {
        return report("""
                behavior f : (b: Date) -> Bool
                let f (b) = %s
                """.formatted(comparison));
    }

    @Test
    void aYearBeyondTheShiftDrawsALineOnTheDateItself() {
        String report = about("Date.year(Date.addDays(1, b)) >= 2027");

        assertTrue(report.contains("measurement: complete"), report);
        assertTrue(report.contains("read as f/b: = 2026-12-31"), report);
    }

    @Test
    void theShiftTurnsTheLineTheOtherWayRound() {
        String report = about("Date.year(Date.addDays(-1, b)) < 2027");

        assertTrue(report.contains("measurement: complete"), report);
        assertTrue(report.contains("read as f/b: = 2027-01-01"), report);
    }

    @Test
    void everyRelationIsReadToTheEnd() {
        for (String relation : new String[] {">=", ">", "<=", "<", "==", "/="}) {
            String report = about("Date.year(Date.addDays(1, b)) " + relation + " 2027");

            assertTrue(report.contains("measurement: complete"), relation + "\n" + report);
        }
    }

    @Test
    void anEqualityIsTheDatesOfTheYearAndSoDrawsBothEnds() {
        String report = about("Date.year(Date.addDays(1, b)) == 2027");

        assertTrue(report.contains("borders 2"), report);
        assertTrue(report.contains("= 2026-12-31"), report);
        assertTrue(report.contains("= 2027-12-31"), report);
    }

    @Test
    void rowsOnBothSidesOfTheLineAreWhatTheProgramComputes() {
        String report = report("""
                behavior f : (b: Date) -> Bool
                let f (b) = Date.year(Date.addDays(1, b)) >= 2027

                example f
                    | "on" : (Date("2026-12-31")) -> true
                    | "off" : (Date("2026-12-30")) -> false
                    | "in" : (Date("2027-06-01")) -> true
                    | "out" : (Date("2026-06-01")) -> false
                """);

        assertTrue(report.contains("obligations 4/4"), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    @Test
    void aPartOfADateThatRepeatsEveryYearIsNotOneLine() {
        String report = about("Date.month(Date.addDays(1, b)) >= 3");

        assertTrue(report.contains("not read"), report);
        assertFalse(report.contains("measurement: complete"), report);
    }

    @Test
    void aYearTheLanguageDoesNotSpellIsLeftUnread() {
        String report = about("Date.year(Date.addDays(1, b)) >= 20000");

        assertTrue(report.contains("not read"), report);
    }

    @Test
    void theYearOfADateThatIsAPositionKeepsItsOwnTerm() {
        String report = about("Date.year(b) >= 2027");

        assertTrue(report.contains("read as f/Date.year(b)"), report);
        assertFalse(report.contains("read as f/b"), report);
    }
}
