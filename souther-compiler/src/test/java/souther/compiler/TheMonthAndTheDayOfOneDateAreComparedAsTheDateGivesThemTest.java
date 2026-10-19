package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The month and the day of a date are two numbers of one place, and not every month goes with
 * every day. A comparison of them is read by the months and days the date has.
 */
class TheMonthAndTheDayOfOneDateAreComparedAsTheDateGivesThemTest {

    private static final String NOT_REACHED = "not shown to reach every value here";

    private static String about(String body) {
        Compilation compilation = Compilation.ofSource("""
                module p

                behavior f : (birthday: Date, on: Date) -> Bool
                let f (birthday, on) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static final String BEFORE_THE_BIRTHDAY =
            "Date.month(on) * 100 + Date.day(on)"
                    + " < Date.month(birthday) * 100 + Date.day(birthday)";

    @Test
    void theMonthsAndDaysOfTwoDatesDivideNeitherOfThem() {
        String report = about(BEFORE_THE_BIRTHDAY);

        assertFalse(report.contains(NOT_REACHED), report);
        for (String term : new String[] {"Date.month(on)", "Date.day(on)",
                "Date.month(birthday)", "Date.day(birthday)"}) {
            assertTrue(report.contains("it relates the value here to another value rather than"
                    + " dividing the values here, about `" + term + "`"), report);
        }
    }

    /**
     * February has no day past the twenty-ninth, so at February every sum of a month and a day is
     * below thirty-two and the month settles the comparison. The thirtieth of February would make
     * it come out the other way, and the month would then be left either way.
     */
    @Test
    void aDayFebruaryDoesNotHaveIsNoWitnessForTheMonth() {
        String report = about("Date.month(on) + Date.day(on) < 32");

        assertTrue(report.contains(NOT_REACHED + ", so which values here settle it on their own"
                + " is not worked out, about `Date.month(on)`"), report);
    }

    /** A way that narrows the month leaves the combinations it lets through, which are not asked
     *  for, so the comparison is read as it was. */
    @Test
    void aMonthTheWayNarrowsIsNotAskedByAllTheCalendarGives() {
        String report = about("if Date.month(on) >= 6 then " + BEFORE_THE_BIRTHDAY + " else false");

        assertTrue(report.contains(NOT_REACHED), report);
    }
}
