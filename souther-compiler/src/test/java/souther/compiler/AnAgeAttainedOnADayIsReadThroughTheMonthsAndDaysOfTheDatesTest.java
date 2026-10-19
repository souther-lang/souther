package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An age worked out from the years of two dates and corrected by their months and days is read as
 * the comparison it is: the difference of the years, and the months and days of the dates, each
 * as a number of its own.
 */
class AnAgeAttainedOnADayIsReadThroughTheMonthsAndDaysOfTheDatesTest {

    private static final String NOT_REACHED = "not shown to reach every value here";

    private static final String AGE = """
            module p

            let ageOn (birthday: Date, on: Date): Int =
                Date.year(on) - Date.year(birthday)
                    - (if Date.month(on) * 100 + Date.day(on)
                            < Date.month(birthday) * 100 + Date.day(birthday)
                       then 1 else 0)

            let attainedAgeOn (birthday: Date, on: Date): Int =
                ageOn(Date.addDays(0 - 1, birthday), on)

            behavior f : (birthday: Date, on: Date) -> Bool
            """;

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String report(String source) {
        Compilation compilation = compiled(source);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void theAgeAttainedOnADayIsReadInTheMonthsAndDaysAndInTheYears() {
        String report = report(AGE + "let f (birthday, on) = attainedAgeOn(birthday, on) >= 60\n");

        assertFalse(report.contains(NOT_REACHED), report);
        assertTrue(report.contains("rather than dividing the values here, about"
                + " `Date.month((birthday -1 days))`"), report);
    }

    /** The comparison of the difference with the age is drawn at its own line, and the month and
     *  day correction at its. */
    @Test
    void aRowIsOfferedAtTheLineOfEachOfThem() {
        Compilation compilation = compiled(AGE
                + "let f (birthday, on) = attainedAgeOn(birthday, on) >= 60\n");
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("p")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();

        for (String comparison : new String[] {"comparison@0:13:52", "comparison@0:6:"}) {
            assertTrue(offered.contains("fills ON point of " + comparison)
                    && offered.contains("fills OFF point of " + comparison), offered);
        }
    }

    /**
     * A way that holds only at the twenty-ninth of February is a month and day that is not in
     * every year, so the years of the date are not left alone by it.
     */
    @Test
    void aWayThatHoldsOnlyAtALeapDayLeavesTheYearsTied() {
        String report = report("""
                module p

                behavior f : (birthday: Date, on: Date) -> Bool
                let f (birthday, on) =
                    if Date.month(on) == 2 && Date.day(on) == 29
                    then Date.year(on) - Date.year(birthday) >= 60 else false
                """);

        assertTrue(report.contains(NOT_REACHED), report);
    }
}
