package souther.compiler;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.IntPredicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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

    /** Each source measured once for the class: the tests here only read what a measurement says,
     *  and four ask the age between forty and sixty-five. */
    private static final Map<String, Compilation> MEASURED = new HashMap<>();

    private static Compilation compiled(String source) {
        return MEASURED.computeIfAbsent(source, each -> {
            Compilation compilation = Compilation.ofSource(each, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            return compilation;
        });
    }

    /** And given back when the class is done with them: a fork keeps its JVM, so what is held
     *  statically is held for every class after this one. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    private static String report(String source) {
        return report(compiled(source));
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void theAgeAttainedOnADayIsReadInTheMonthsAndDaysAndInTheYears() {
        String report = report(BETWEEN_FORTY_AND_SIXTY_FIVE);

        assertFalse(report.contains(NOT_REACHED), report);
        assertTrue(report.contains("rather than dividing the values here, about"
                + " `Date.month((birthday -1 days))`"), report);
    }

    /** The age of the pair as the calendar works it out, and not as the reading does. */
    private static int ageAttained(LocalDate birthday, LocalDate on) {
        LocalDate dayBefore = birthday.minusDays(1);
        int difference = on.getYear() - dayBefore.getYear();
        return difference - (beforeTheDay(birthday, on) ? 1 : 0);
    }

    /** Whether the day is before the day of the year the age is attained on. */
    private static boolean beforeTheDay(LocalDate birthday, LocalDate on) {
        LocalDate dayBefore = birthday.minusDays(1);
        return on.getMonthValue() * 100 + on.getDayOfMonth()
                < dayBefore.getMonthValue() * 100 + dayBefore.getDayOfMonth();
    }

    /**
     * The rows offered stand at both sides of each line of the age, and at both sides of the
     * correction by the month and day where the years are as far apart as the line: the same
     * difference of years, an age one short of the line before the day and at the line on or
     * after it.
     */
    @Test
    void theRowsOfferedStandAtBothSidesOfTheAgeAndOfTheMonthAndDayCorrection() {
        Compilation compilation = compiled(BETWEEN_FORTY_AND_SIXTY_FIVE);
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("p")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();

        Set<String> atTheLines = new HashSet<>();
        for (String row : offered.lines().filter(each -> each.contains("Date(\"")).toList()) {
            List<LocalDate> dates = new ArrayList<>();
            int at = 0;
            while ((at = row.indexOf("Date(\"", at)) >= 0) {
                int end = row.indexOf('"', at + 6);
                dates.add(LocalDate.parse(row.substring(at + 6, end)));
                at = end;
            }
            int apart = dates.get(1).getYear() - dates.get(0).minusDays(1).getYear();
            atTheLines.add(apart + " apart, " + ageAttained(dates.get(0), dates.get(1)));
        }

        assertTrue(atTheLines.containsAll(List.of(
                "40 apart, 39", "40 apart, 40", "65 apart, 64", "65 apart, 65")),
                atTheLines + "\n" + offered);
    }

    /**
     * What each row offered for a way that states the age at two lines is answered, worked out
     * apart from the reading and put to the program, with a row at each side of each line.
     *
     * <p>The rows come with the answer the calendar gives for the age, and are written as the
     * examples of the behavior: the program is run on each and an answer that is not the one
     * written is an error. So a row the reading placed wrongly, at a date where the age is not
     * what the line was drawn at, shows as an answer that differs, and what is offered is
     * covered by what was written, with no point left without a row.
     */
    @Test
    void theRowsOfferedForTwoComparisonsOfOneAgeAreAnsweredAsTheCalendarWorksTheAgeOut() {
        assertRowsAreAnsweredAsTheCalendarWorksTheAgeOut(BETWEEN_FORTY_AND_SIXTY_FIVE,
                age -> age >= 40 && age < 65, 39, 40, 64, 65);
    }

    /**
     * @param reached the ages the rows offered must include, one at each side of each line
     */
    private static void assertRowsAreAnsweredAsTheCalendarWorksTheAgeOut(
            String behavior, IntPredicate expected, Integer... reached) {
        Compilation offering = compiled(behavior);
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(offering.db(), OfferingRequest.overTheModule("p")),
                Map.of(), SourceRendering.namedByIdentity(offering.texts()), offering.db())
                .text();

        StringBuilder examples = new StringBuilder();
        Set<Integer> ages = new HashSet<>();
        int rows = 0;
        for (String line : offered.lines().filter(each -> each.contains("Date(\"")).toList()) {
            List<LocalDate> dates = new ArrayList<>();
            int at = 0;
            while ((at = line.indexOf("Date(\"", at)) >= 0) {
                int end = line.indexOf('"', at + 6);
                dates.add(LocalDate.parse(line.substring(at + 6, end)));
                at = end;
            }
            ages.add(ageAttained(dates.get(0), dates.get(1)));
            examples.append("    | (Date(\"").append(dates.get(0)).append("\"), Date(\"")
                    .append(dates.get(1)).append("\")) -> ")
                    .append(expected.test(ageAttained(dates.get(0), dates.get(1)))).append('\n');
            rows++;
        }
        assertTrue(rows > 0, offered);
        assertTrue(ages.containsAll(List.of(reached)), ages + "\n" + offered);

        Compilation answered = compiled(behavior + "\nexample f\n" + examples);
        String report = report(answered);

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
     * stated at one level and asked at another, and are read by how far apart they are.
     */
    @Test
    void theCorrectionOneComparisonStatesAndAnotherAsksAgainIsReadAlongWaysThatStateYearsToo() {
        String report = report(BETWEEN_FORTY_AND_SIXTY_FIVE);

        assertFalse(report.contains(NOT_REACHED + ", so which values here settle it on their own"
                + " is not worked out, about `Date.month(on)`"), report);
        assertFalse(report.contains(NOT_REACHED + ", so which values here settle it on their own"
                + " is not worked out, about `Date.day(on)`"), report);
        assertFalse(report.contains(NOT_REACHED + ", so which values here settle it on their own"
                + " is not worked out, about `Date.year(on)`"), report);
        assertFalse(report.contains(NOT_REACHED + ", so which values here settle it on their own"
                + " is not worked out, about `Date.year((birthday -1 days))`"), report);
    }

    /** The chain measured once, for the tests that read it. A measure of it is most of what they
     *  cost, and what each asks is of this one. */
    private static final class Measured {
        static final Compilation CHAIN_OF_AGES = compiled(CHAIN);
        static final String REPORT = report(CHAIN_OF_AGES);
    }

    /**
     * Arms of an {@code if} chain beside a flag add ways to the third comparison, most of which
     * ask the age to be at least seventy and below nineteen at once. Those are no way and do not
     * count against the figure, so each of the ways left is looked along, and the age the
     * {@code let} binds is read in the years of the dates at each line it is compared at.
     */
    @Test
    void aChainOfAgeComparisonsBesideAFlagIsReadInTheYearsMonthsAndDays() {
        assertFalse(Measured.REPORT.contains(NOT_REACHED), Measured.REPORT);
    }

    private static final String CHAIN = AGE.replace(
            "behavior f : (birthday: Date, on: Date) -> Bool\n", "") + """
            behavior f : (birthday: Date, on: Date, ascendant: Bool) -> Int
            let f (birthday, on, ascendant) = {
                let age = attainedAgeOn(birthday, on)
                if age >= 70 && ascendant then 3
                else if age >= 70 then 2
                else if age >= 19 then 1
                else 0
            }
            """;

    /** The class of a person of {@code age}, as the chain of comparisons is meant to put it. */
    private static int classOf(int age, boolean ascendant) {
        if (age >= 70 && ascendant) {
            return 3;
        }
        if (age >= 70) {
            return 2;
        }
        return age >= 19 ? 1 : 0;
    }

    /** One example row, answered with the class the calendar's age and the flag give. */
    private static void example(StringBuilder into, LocalDate birthday, LocalDate on,
                                boolean ascendant) {
        into.append("    | (Date(\"").append(birthday).append("\"), Date(\"").append(on)
                .append("\"), ").append(ascendant).append(") -> ")
                .append(classOf(ageAttained(birthday, on), ascendant)).append('\n');
    }

    /**
     * The rows offered stand at both sides of each line of the age, and the class each is
     * answered is the one the calendar's age and the flag give.
     *
     * <p>The answers are worked out here, apart from the compiler, and the rows are written back
     * as examples the program is run on: an answer that is not the program's is an error. That
     * holds the working out of the age, the chain of comparisons and the rows put at its lines to
     * one account of the calendar together, which no test of one of them alone does. The rows run
     * are the ones at the lines — the rows offered, and past seventy the day each age is attained
     * and the day before at both values of the flag, which the rows offered stand at only where a
     * comparison asks it.
     */
    @Test
    void theRowsOfferedForAChainOfAgeComparisonsAreAnsweredAsTheCalendarWorksTheClassOut() {
        Compilation offering = Measured.CHAIN_OF_AGES;
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(offering.db(), OfferingRequest.overTheModule("p")),
                Map.of(), SourceRendering.namedByIdentity(offering.texts()), offering.db())
                .text();

        Pattern row = Pattern.compile(
                "Date\\(\"([^\"]+)\"\\), Date\\(\"([^\"]+)\"\\), (true|false)");
        StringBuilder examples = new StringBuilder();
        Set<Integer> ages = new HashSet<>();
        for (String line : offered.lines().toList()) {
            Matcher found = row.matcher(line);
            if (found.find()) {
                LocalDate birthday = LocalDate.parse(found.group(1));
                LocalDate on = LocalDate.parse(found.group(2));
                ages.add(ageAttained(birthday, on));
                example(examples, birthday, on, Boolean.parseBoolean(found.group(3)));
            }
        }
        assertTrue(ages.containsAll(List.of(18, 19, 69, 70)),
                () -> "a row at each side of each line: " + ages + "\n" + offered);

        LocalDate born = LocalDate.of(1950, 6, 15);
        for (int age : List.of(69, 70)) {
            LocalDate attained = born.minusDays(1).plusYears(age);
            for (LocalDate on : List.of(attained, attained.minusDays(1))) {
                example(examples, born, on, true);
                example(examples, born, on, false);
            }
        }

        // Run and not measured: an example whose answer is not the program's is an error, which
        // is all this asks of the rows.
        Compilation answered = Compilation.ofSource(CHAIN + "\nexample f\n" + examples, "Main");
        answered.answerEverything();
        assertEquals(0, answered.errors().size(), () -> answered.errors() + "\n" + examples);
    }

    /**
     * The years of the two dates are tied by the age, so the year of the day is not left the whole
     * of a year's range by the year of the birthday still to be chosen: every point of the month
     * and day correction at seventy, where the flag is asked beside the age, is offered a row,
     * each where the calendar puts it.
     */
    @Test
    void everyPointOfTheCorrectionOfAnAgeBesideAFlagIsOfferedARow() {
        Compilation compilation = Measured.CHAIN_OF_AGES;
        String report = Measured.REPORT;
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("p")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();

        assertFalse(report.contains("no row composed for"), report);

        Pattern row = Pattern.compile(
                "Date\\(\"([^\"]+)\"\\), Date\\(\"([^\"]+)\"\\), (true|false)");
        Set<String> points = new HashSet<>();
        for (String line : offered.lines().toList()) {
            Matcher found = row.matcher(line);
            if (found.find()) {
                LocalDate birthday = LocalDate.parse(found.group(1));
                LocalDate on = LocalDate.parse(found.group(2));
                boolean ascendant = Boolean.parseBoolean(found.group(3));
                int age = ageAttained(birthday, on);
                points.add(age + " " + (beforeTheDay(birthday, on) ? "before" : "on or after")
                        + " " + ascendant);
            }
        }
        assertFalse(points.isEmpty(), offered);
        // A row at each side of the correction by the month and day where the age is seventy, and
        // one at each value of the flag from there on: the points the report would name if one of
        // them had no row, asked of the rows themselves. The rows stand at the points of each
        // comparison and not at every way the flag combines with them.
        assertTrue(points.stream().anyMatch(each -> each.startsWith("70 before")), points.toString());
        assertTrue(points.stream().anyMatch(each -> each.startsWith("70 on or after")),
                points.toString());
        assertTrue(points.contains("70 on or after true") && points.contains("70 on or after false"),
                points.toString());
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
