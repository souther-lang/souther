package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.IntPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
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

    /** The age of the pair as the calendar works it out, and not as the reading does. */
    private static int ageAttained(LocalDate birthday, LocalDate on) {
        LocalDate dayBefore = birthday.minusDays(1);
        int difference = on.getYear() - dayBefore.getYear();
        boolean beforeTheDay = on.getMonthValue() * 100 + on.getDayOfMonth()
                < dayBefore.getMonthValue() * 100 + dayBefore.getDayOfMonth();
        return difference - (beforeTheDay ? 1 : 0);
    }

    /**
     * The rows offered stand at both sides of the line of the age, and at both sides of the
     * correction by the month and day where the years are sixty apart: the same difference of
     * years, an age of fifty-nine before the day and of sixty on or after it.
     */
    @Test
    void theRowsOfferedStandAtBothSidesOfTheAgeAndOfTheMonthAndDayCorrection() {
        Compilation compilation = compiled(AGE
                + "let f (birthday, on) = attainedAgeOn(birthday, on) >= 60\n");
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("p")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();

        Set<Integer> ages = new HashSet<>();
        boolean sixtyYearsApartBefore = false;
        boolean sixtyYearsApartOnOrAfter = false;
        for (String row : offered.lines().filter(each -> each.contains("Date(\"")).toList()) {
            List<LocalDate> dates = new ArrayList<>();
            int at = 0;
            while ((at = row.indexOf("Date(\"", at)) >= 0) {
                int end = row.indexOf('"', at + 6);
                dates.add(LocalDate.parse(row.substring(at + 6, end)));
                at = end;
            }
            int age = ageAttained(dates.get(0), dates.get(1));
            ages.add(age);
            if (dates.get(1).getYear() - dates.get(0).minusDays(1).getYear() == 60) {
                sixtyYearsApartBefore |= age == 59;
                sixtyYearsApartOnOrAfter |= age == 60;
            }
        }

        assertTrue(ages.contains(59) && ages.contains(60), ages + "\n" + offered);
        assertTrue(sixtyYearsApartBefore && sixtyYearsApartOnOrAfter, offered);
    }

    /**
     * What each row offered is answered, worked out apart from the reading and put to the program.
     *
     * <p>The rows come with the answer the calendar gives for the age, and are written as the
     * examples of the behavior: the program is run on each and an answer that is not the one
     * written is an error. So a row the reading placed wrongly, at a date where the age is not
     * what the line was drawn at, shows as an answer that differs, and what is offered is
     * covered by what was written, with no point left without a row.
     */
    @Test
    void theRowsOfferedAreAnsweredAsTheCalendarWorksTheAgeOut() {
        assertRowsAreAnsweredAsTheCalendarWorksTheAgeOut(
                AGE + "let f (birthday, on) = attainedAgeOn(birthday, on) >= 60\n",
                age -> age >= 60);
    }

    /** The same of a way that states the age at two lines. */
    @Test
    void theRowsOfferedForTwoComparisonsOfOneAgeAreAnsweredAsTheCalendarWorksTheAgeOut() {
        assertRowsAreAnsweredAsTheCalendarWorksTheAgeOut(BETWEEN_FORTY_AND_SIXTY_FIVE,
                age -> age >= 40 && age < 65);
    }

    private static void assertRowsAreAnsweredAsTheCalendarWorksTheAgeOut(
            String behavior, IntPredicate expected) {
        Compilation offering = compiled(behavior);
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(offering.db(), OfferingRequest.overTheModule("p")),
                Map.of(), SourceRendering.namedByIdentity(offering.texts()), offering.db())
                .text();

        StringBuilder examples = new StringBuilder();
        int rows = 0;
        for (String line : offered.lines().filter(each -> each.contains("Date(\"")).toList()) {
            List<LocalDate> dates = new ArrayList<>();
            int at = 0;
            while ((at = line.indexOf("Date(\"", at)) >= 0) {
                int end = line.indexOf('"', at + 6);
                dates.add(LocalDate.parse(line.substring(at + 6, end)));
                at = end;
            }
            examples.append("    | (Date(\"").append(dates.get(0)).append("\"), Date(\"")
                    .append(dates.get(1)).append("\")) -> ")
                    .append(expected.test(ageAttained(dates.get(0), dates.get(1)))).append('\n');
            rows++;
        }
        assertTrue(rows > 0, offered);

        Compilation answered = compiled(behavior + "\nexample f\n" + examples);
        String report = report(behavior + "\nexample f\n" + examples);

        assertEquals(0, answered.errors().size(), report + "\n" + examples);
        assertFalse(report.contains("no row is at"), report);
    }

    /**
     * A declaration that relates the two dates ties their months and days to each other, so
     * neither is a number apart from the other's.
     */
    @Test
    void aDeclarationThatRelatesTheDatesKeepsTheirPartsTied() {
        String report = report("""
                module p

                data Span = { birthday: Date, on: Date }
                    invariant Date.daysBetween(birthday, on) >= 0

                behavior f : (span: Span) -> Bool
                let f (span) =
                    Date.month(span.on) * 100 + Date.day(span.on)
                        < Date.month(span.birthday) * 100 + Date.day(span.birthday)
                """);

        assertFalse(report.contains("rather than dividing the values here, about"
                + " `Date.month(span.on)`"), report);
    }

    /**
     * Two conditions on the year that each hold at many years and together at one: 2025, which has
     * no twenty-ninth of February. At February every month and day sum is below thirty-one, so
     * the month settles the comparison there, and it would not were the twenty-ninth a witness.
     */
    @Test
    void conditionsOnTheYearThatHoldTogetherAtOneYearGiveTheMonthsAndDaysOfThatYear() {
        String report = report("""
                module p

                behavior f : (on: Date) -> Bool
                let f (on) =
                    if Date.year(on) >= 2025 && Date.year(on) <= 2025
                    then Date.month(on) + Date.day(on) < 31 else false
                """);

        assertFalse(report.contains("rather than dividing the values here, about"
                + " `Date.month(on)`"), report);
    }

    private static final String BETWEEN_FORTY_AND_SIXTY_FIVE = AGE
            + "let f (birthday, on) = attainedAgeOn(birthday, on) >= 40"
            + " && attainedAgeOn(birthday, on) < 65\n";

    /**
     * Two comparisons of one age state the months and days of the dates, and their years, along
     * one way. The first comparison states the correction by the months and days that the second
     * asks again, so the way decides it and the months and days are read there. The years are
     * stated at one level and asked at another, and are not read.
     */
    @Test
    void theCorrectionOneComparisonStatesAndAnotherAsksAgainIsReadAlongWaysThatStateYearsToo() {
        String report = report(BETWEEN_FORTY_AND_SIXTY_FIVE);

        assertFalse(report.contains(NOT_REACHED + ", so which values here settle it on their own"
                + " is not worked out, about `Date.month(on)`"), report);
        assertFalse(report.contains(NOT_REACHED + ", so which values here settle it on their own"
                + " is not worked out, about `Date.day(on)`"), report);
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
