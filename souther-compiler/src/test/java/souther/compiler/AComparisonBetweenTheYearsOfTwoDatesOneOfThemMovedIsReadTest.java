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
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The year of a date moved by days is a number of the place the date was moved from, so a
 * comparison of it with the year of another date is read like any other comparison of two numbers.
 *
 * <p>What is held here is the two directions of that: that a row is read as the point it stands at
 * (the examples are put at each side of the line the dates give, and the report is asked whether
 * every point has its row), and that the program the rows run is the one the expected answers were
 * worked out for ({@code java.time}, and not the reading's own arithmetic).
 */
class AComparisonBetweenTheYearsOfTwoDatesOneOfThemMovedIsReadTest {

    private static final String ATTAINED =
            "Date.year(on) - Date.year(Date.addDays(0 - 1, birthday)) >= 60";

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String about(String body) {
        return report(compiled("""
                module p

                behavior f : (birthday: Date, on: Date) -> Bool
                let f (birthday, on) = %s
                """.formatted(body)));
    }

    @Test
    void theComparisonOfTheIssueIsReadAndNotLeftUnread() {
        String report = about(ATTAINED);

        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("not read"), report);
        assertTrue(report.contains("Date.year((birthday -1 days))"), report);
    }

    @Test
    void theYearOfTheOtherDateAloneIsReadToo() {
        String report = about("Date.year(on) >= Date.year(Date.addDays(0 - 1, birthday))");

        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("not read"), report);
    }

    @Test
    void theMovedYearIsReadOnWhicheverSideItStandsOn() {
        String first = about("Date.year(on) > Date.year(Date.addDays(1, birthday))");
        String turned = about("Date.year(Date.addDays(1, birthday)) < Date.year(on)");

        assertTrue(first.contains("measurement: complete"), first);
        assertTrue(turned.contains("measurement: complete"), turned);
        // The line is the same one said of the number the rule was written about first, so what
        // differs is which of the two is the subject and not how many points there are.
        assertEquals(bordersOf(first).size(), bordersOf(turned).size(), turned);
        assertEquals(4, bordersOf(turned).size(), turned);
    }

    private static List<String> bordersOf(String report) {
        return report.lines().filter(each -> each.contains("read as ")).sorted().toList();
    }

    /** Whether the dates attained their age on that day, by the calendar and not by the rule. */
    private static boolean attained(LocalDate birthday, LocalDate on) {
        return on.getYear() - birthday.minusDays(1).getYear() >= 60;
    }

    /**
     * A row at each point of the comparison, and each of them answers what the calendar says.
     *
     * <p>The birthdays are the ones where moving the date back a day changes the year, and the
     * ones where it does not, since the line is where the two differ.
     */
    @Test
    void aRowAtEachPointOfTheComparisonIsTheOneTheReadingSaysItIs() {
        List<LocalDate> birthdays = List.of(LocalDate.of(1950, 1, 1), LocalDate.of(1950, 1, 2),
                LocalDate.of(1960, 12, 31), LocalDate.of(1952, 2, 29));
        StringBuilder rows = new StringBuilder();
        for (LocalDate birthday : birthdays) {
            // The year the shifted date is in, and the years of `on` that put the difference at 59,
            // 60 and 61 and well away from it on either side.
            int base = birthday.minusDays(1).getYear();
            for (int difference : new int[] {20, 58, 59, 60, 61, 90}) {
                LocalDate on = LocalDate.of(base + difference, 6, 15);
                rows.append("    | (Date(\"").append(birthday).append("\"), Date(\"").append(on)
                        .append("\")) -> ").append(attained(birthday, on)).append('\n');
            }
        }
        Compilation compilation = compiled("""
                module p

                behavior f : (birthday: Date, on: Date) -> Bool
                let f (birthday, on) = %s

                example f
                %s""".formatted(ATTAINED, rows));
        String report = report(compilation);

        assertEquals(0, compilation.errors().size(), report);
        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("no row is at the ON point"), report);
        assertFalse(report.contains("no row is at the OFF point"), report);
    }

    /**
     * Which point a row is at turns on the year of the date a day back, which for a birthday on the
     * first of January is the year before.
     *
     * <p>Rows only at a difference of sixty and above, read for the birthdays that are the first
     * of January: the point just under the line is where nothing stands, and a reading that took
     * the year of the birthday itself would put the row at sixty one place down and find it.
     */
    @Test
    void aBirthdayOnTheFirstOfJanuaryIsReadAtTheYearBeforeIt() {
        StringBuilder rows = new StringBuilder();
        for (int difference : new int[] {20, 60, 61, 90}) {
            LocalDate birthday = LocalDate.of(1950, 1, 1);
            LocalDate on = LocalDate.of(birthday.minusDays(1).getYear() + difference, 6, 15);
            rows.append("    | (Date(\"").append(birthday).append("\"), Date(\"").append(on)
                    .append("\")) -> ").append(attained(birthday, on)).append('\n');
        }
        Compilation compilation = compiled("""
                module p

                behavior f : (birthday: Date, on: Date) -> Bool
                let f (birthday, on) = %s

                example f
                %s""".formatted(ATTAINED, rows));
        String report = report(compilation);

        assertEquals(0, compilation.errors().size(), report);
        assertTrue(report.contains("no row is at the OFF point"), report);
        assertFalse(report.contains("no row is at the ON point"), report);
    }

    /** What the year of a date a day back is, standing beside the year of the date itself. */
    @Test
    void theYearOfADateAndTheYearOfItADayBackAreTwoNumbersOfOneDate() {
        String report = about("Date.year(birthday) == Date.year(Date.addDays(0 - 1, birthday))");

        assertTrue(report.contains("Date.year(birthday)"), report);
        assertTrue(report.contains("Date.year((birthday -1 days))"), report);
        assertTrue(report.contains("measurement: complete"), report);
    }

    /**
     * The rows offered for a class are dates the class holds, which is what every number taken of
     * them reading back as the one asked for comes to.
     */
    @Test
    void theRowsOfferedForTheComparisonAreAtTheYearsItAsksFor() {
        Compilation compilation = compiled("""
                module p

                behavior f : (birthday: Date, on: Date) -> Bool
                let f (birthday, on) = %s
                """.formatted(ATTAINED));
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("p")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();

        List<int[]> yearsOfEach = new ArrayList<>();
        offered.lines().filter(each -> each.contains("Date(\"")).forEach(each -> {
            List<LocalDate> dates = new ArrayList<>();
            int at = 0;
            while ((at = each.indexOf("Date(\"", at)) >= 0) {
                int end = each.indexOf('"', at + 6);
                dates.add(LocalDate.parse(each.substring(at + 6, end)));
                at = end;
            }
            yearsOfEach.add(new int[] {dates.get(0).minusDays(1).getYear(),
                    dates.get(1).getYear()});
        });

        assertEquals(4, yearsOfEach.size(), offered);
        List<Integer> differences = yearsOfEach.stream().map(each -> each[1] - each[0]).sorted()
                .toList();
        // Under, at, over and well under the line the two years' difference draws at sixty.
        assertTrue(differences.contains(59), differences + "\n" + offered);
        assertTrue(differences.contains(60), differences + "\n" + offered);
        assertTrue(differences.stream().anyMatch(each -> each > 60), differences + "\n" + offered);
        assertTrue(differences.stream().anyMatch(each -> each < 59), differences + "\n" + offered);
    }

    /**
     * The year of a moved date and the month of the date itself are asked of one date, so a row is
     * offered that answers both, and the question is not left as one nothing here solves.
     */
    @Test
    void aMovedYearAndAMonthOfTheDateItselfAreOneQuestion() {
        Compilation compilation = compiled("""
                module p

                behavior f : (birthday: Date) -> Bool
                let f (birthday) =
                    Date.year(Date.addDays(0 - 1, birthday)) == 2026 && Date.month(birthday) == 1
                """);
        String report = report(compilation);
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("p")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();

        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("not read"), report);
        // Moved a day back it is in 2026, and it is in January: the second of January to the first
        // of February. A row there is the one that makes both true.
        assertTrue(offered.lines().anyMatch(each -> each.contains("Date(\"2026-01-")
                        && !each.contains("2026-01-01") || each.contains("Date(\"2026-02-01")),
                "no row is offered where both hold:\n" + offered);
    }

    /** A date moved by nothing is the date: its year is the number the date's own year is. */
    @Test
    void aDateMovedByNothingIsTheDate() {
        String moved = about("Date.year(Date.addDays(0, birthday)) >= 2027");
        String itself = about("Date.year(birthday) >= 2027");

        assertTrue(moved.contains("Date.year(birthday)"), moved);
        assertFalse(moved.contains("days"), moved);
        assertEquals(bordersOf(itself), bordersOf(moved), moved);
    }

    /** Moved and moved back is the same number only where the first move is one the date makes. */
    @Test
    void aShiftUndoneKeepsWhereItIsDefined() {
        String report = about("Date.year(Date.addDays(0 - 1, Date.addDays(1, birthday))) >= 2027");

        assertTrue(report.contains("measurement: complete"), report);
        assertTrue(report.contains("days, defined from"), report);
    }

    @Test
    void aShiftUndoneAtTheEndOfTheRangeAbortsAndIsNoRowThatReachedALine() {
        Compilation past = compiled("""
                module p

                behavior f : (birthday: Date) -> Bool
                let f (birthday) = Date.year(Date.addDays(0 - 1, Date.addDays(1, birthday))) >= 2027

                example f
                    | (Date("+999999999-12-31")) -> true
                """);

        assertEquals(1, past.errors().size(), "the program aborts there: " + report(past));

        String offered = GeneratedRows.of(
                Adequacy.offeredFor(past.db(), OfferingRequest.overTheModule("p")), Map.of(),
                SourceRendering.namedByIdentity(past.texts()), past.db()).text();
        assertFalse(offered.contains("+999999999-12-31"),
                "no row is offered at the date whose first shift aborts: " + offered);
    }

    /** Two shifts that are one shift are one number, wherever the chain is written. */
    @Test
    void severalShiftsAreOneNumberWhereTheyAreOneShift() {
        String chained =
                about("Date.year(Date.addDays(0 - 1, Date.addDays(31, birthday))) >= 2027");
        String once = about("Date.year(Date.addDays(30, birthday)) >= 2027");

        assertTrue(chained.contains("measurement: complete"), chained);
        assertTrue(once.contains("measurement: complete"), once);
        assertTrue(chained.contains("+30 days"), chained);
    }

    /** A month repeats every year, so a shifted one is no number the line is drawn on. */
    @Test
    void aMonthOfAMovedDateIsStillNotRead() {
        String report = about("Date.month(Date.addDays(1, birthday)) >= 3");

        assertTrue(report.contains("not read"), report);
        assertFalse(report.contains("measurement: complete"), report);
    }

    /** A count another input supplies is no shift of one position: it is a number of two. */
    @Test
    void aShiftByACountAnotherInputSuppliesIsNotAShiftOfOnePosition() {
        Compilation compilation = compiled("""
                module p

                behavior f : (birthday: Date, days: Int) -> Bool
                let f (birthday, days) = Date.year(Date.addDays(days, birthday)) >= 2027
                """);
        String report = report(compilation);

        assertFalse(report.contains("Date.year((birthday"), report);
        assertTrue(report.contains("measurement: complete"), report);
    }
}
