package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.time.LocalDate;
import java.time.YearMonth;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The month and the day of a date moved by a count of days written out are numbers of the date it
 * was moved from, read as the month and the day of the date itself are.
 *
 * <p>Held in the two directions the year of a moved date is held in. Rows are put on each side of
 * every month or day the comparison turns over at, with the answers worked out by {@code java.time},
 * so a row whose answer the program does not give is an error; and the report is asked whether
 * every point has its row, so a point the reading put a day away from where the program turns has
 * none.
 */
class AMonthOrADayOfAShiftedDateIsReadTest {

    private static final String[] RELATIONS = {">=", ">", "<=", "<", "==", "/="};

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

    private static int partOf(String part, LocalDate date) {
        return part.equals("month") ? date.getMonthValue() : date.getDayOfMonth();
    }

    private static boolean holds(int found, String relation, int value) {
        return switch (relation) {
            case ">=" -> found >= value;
            case ">" -> found > value;
            case "<=" -> found <= value;
            case "<" -> found < value;
            case "==" -> found == value;
            default -> found != value;
        };
    }

    /**
     * Dates whose moved date is at the first and the last of every month of a leap year and of the
     * February and March after it, and, for a day, at the days either side of the one compared
     * with: every month and every day a comparison of either can turn over at has a row each side.
     */
    private static Set<LocalDate> datesAround(String part, int value, int shift) {
        Set<LocalDate> dates = new LinkedHashSet<>();
        List<YearMonth> months = new ArrayList<>();
        for (int month = 1; month <= 12; month++) {
            months.add(YearMonth.of(2024, month));
        }
        months.add(YearMonth.of(2025, 2));
        months.add(YearMonth.of(2025, 3));
        for (YearMonth month : months) {
            Set<Integer> days = new TreeSet<>(List.of(1, month.lengthOfMonth()));
            if (part.equals("day")) {
                for (int day : new int[] {value - 1, value, value + 1}) {
                    if (1 <= day && day <= month.lengthOfMonth()) {
                        days.add(day);
                    }
                }
            }
            for (int day : days) {
                dates.add(month.atDay(day).minusDays(shift));
            }
        }
        return dates;
    }

    private static String source(String comparison, String part, int shift, String relation,
                                 int value, Set<LocalDate> dates) {
        StringBuilder rows = new StringBuilder();
        for (LocalDate date : dates) {
            rows.append("    | (Date(\"").append(date).append("\")) -> ")
                    .append(holds(partOf(part, date.plusDays(shift)), relation, value))
                    .append('\n');
        }
        return """
                module m

                behavior f : (b: Date) -> Bool
                let f (b) = %s

                example f
                %s""".formatted(comparison, rows);
    }

    /** The lines of {@code report} that say how far it was measured and what it comes to. */
    private static List<String> verdicts(String report) {
        return report.lines().filter(line -> line.contains("measurement: ")
                || line.startsWith("adequacy: ")).toList();
    }

    /**
     * Every relation, at a month or a day inside the calendar's and at its last, is measured as
     * the same comparison of the date's own part is, and the rows on each side of each line leave
     * no point without one.
     */
    @Test
    void everyRelationHoldsAtEachLineAndOnBothSidesOfIt() {
        for (String part : List.of("month", "day")) {
            int[] values = part.equals("month") ? new int[] {3, 12} : new int[] {1, 29, 31};
            for (String relation : RELATIONS) {
                for (int value : values) {
                    String own = "Date.%s(b) %s %d".formatted(part, relation, value);
                    String itself = report(compiled(source(own, part, 0, relation, value,
                            datesAround(part, value, 0))));
                    for (int shift : new int[] {1, -1, 30}) {
                        String comparison = "Date.%s(Date.addDays(%d, b)) %s %d"
                                .formatted(part, shift, relation, value);
                        Compilation compilation = compiled(source(comparison, part, shift,
                                relation, value, datesAround(part, value, shift)));
                        String report = report(compilation);
                        String where = comparison + "\n" + report + "\n" + own + "\n" + itself;

                        assertEquals(0, compilation.errors().size(), where);
                        assertFalse(report.contains("no row is at"), where);
                        assertFalse(report.contains("not read"), where);
                        assertEquals(verdicts(itself), verdicts(report), where);
                    }
                }
            }
        }
    }

    /** The line is drawn on the month of the moved date, and not on the date or its own month. */
    @Test
    void theLineIsDrawnOnTheMonthOfTheMovedDate() {
        String report = report(compiled("""
                module m

                behavior f : (b: Date) -> Bool
                let f (b) = Date.month(Date.addDays(1, b)) >= 3
                """));

        assertTrue(report.contains("read as f/Date.month((b +1 days)): = 3"), report);
        assertTrue(report.contains("read as f/Date.month((b +1 days)): = 2"), report);
        assertFalse(report.contains("read as f/b"), report);
        assertFalse(report.contains("read as f/Date.month(b)"), report);
    }

    /**
     * The rows offered for a month of a moved date are dates whose moved date is in the month of
     * each point: the day before the first of March for the line itself, and the day before the
     * last of January for the month below it.
     */
    @Test
    void theRowsOfferedAreDatesWhoseMovedDateIsInTheMonthOfEachPoint() {
        Compilation compilation = compiled("""
                module m

                behavior f : (b: Date) -> Bool
                let f (b) = Date.month(Date.addDays(1, b)) >= 3
                """);
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("m")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();

        assertTrue(offered.contains("Date(\"2000-02-29\")"), offered);
        assertTrue(offered.contains("Date(\"2000-01-31\")"), offered);
    }

    /** The day before the first of March is the twenty-ninth of February in a leap year. */
    @Test
    void theDayBeforeTheFirstOfMarchInALeapYearIsTheTwentyNinth() {
        String report = report(compiled("""
                module m

                behavior f : (b: Date) -> Bool
                let f (b) = Date.day(Date.addDays(0 - 1, b)) == 29 && Date.month(b) == 3

                example f
                    | (Date("2024-03-01")) -> true
                    | (Date("2025-03-01")) -> false
                    | (Date("2024-03-02")) -> false
                    | (Date("2024-04-30")) -> false
                """));

        assertTrue(report.contains("measurement: complete"), report);
        assertTrue(report.contains("Date.day((b -1 days))"), report);
    }

    private static final String AGE = """
            module m

            data AgeBand = Young | Old

            let ageOn (birthday: Date, on: Date): Int =
                Date.year(on) - Date.year(birthday)
                    - (if Date.month(on) * 100 + Date.day(on)
                            < Date.month(birthday) * 100 + Date.day(birthday)
                       then 1 else 0)

            behavior bandOf : (birthday: Date, on: Date%s) -> AgeBand

            let bandOf (birthday, on%s) =
                if ageOn(%s, on) >= 65 then Old else Young
            %s""";

    /** Rows whose answer is the same whether the age is worked out from the birthday or from the
     *  day before it. */
    private static final String AGE_ROWS = """

            example bandOf
                | (Date("1950-04-01"), Date("2026-04-01")) -> Old
                | (Date("1990-04-01"), Date("2026-04-01")) -> Young
            """;

    /** What a report leaves unread, said of the birthday whichever date stands for it. */
    private static Set<String> leftUnread(String report, String birthday) {
        Set<String> unread = new TreeSet<>();
        report.lines().filter(line -> line.strip().startsWith("· not read"))
                .map(line -> line.replace(birthday, "birthday")
                        .replaceAll("comparison@\\d+:\\d+", "comparison")
                        .replaceAll("ageOn@\\d+:\\d+", "ageOn"))
                .forEach(unread::add);
        return unread;
    }

    /**
     * An age worked out from the day before a birthday is read as the age worked out from the
     * birthday is: the condition of the {@code if} is taken apart into the month and the day of
     * the moved date, and nothing is left unread that is not left unread of the birthday itself.
     */
    @Test
    void anAgeFromTheDayBeforeABirthdayIsReadAsAnAgeFromTheBirthday() {
        String moved = report(compiled(AGE.formatted("", "", "Date.addDays(0 - 1, birthday)",
                AGE_ROWS)));
        String itself = report(compiled(AGE.formatted("", "", "birthday", AGE_ROWS)));

        assertFalse(moved.contains("written in a form this compiler does not read"), moved);
        assertFalse(moved.contains("what it says about the values here is not worked out"),
                moved);
        assertTrue(moved.contains("Date.month((birthday -1 days))"), moved);
        assertTrue(moved.contains("Date.day((birthday -1 days))"), moved);
        assertEquals(leftUnread(itself, "birthday"),
                leftUnread(moved, "(birthday -1 days)"), moved);
    }

    /**
     * A birthday moved by a count another input supplies is no moved date of one position, so the
     * condition about its month and its day is no comparison of numbers this reads, and the age
     * is not read as if it were.
     */
    @Test
    void aBirthdayMovedByACountAnInputSuppliesIsNotReadAsOneMovedByADay() {
        String report = report(compiled(AGE.formatted(", lag: Int", ", lag",
                "Date.addDays(0 - lag, birthday)", "")));

        assertTrue(report.contains("not read"), report);
        assertFalse(report.contains("measurement: complete"), report);
        assertFalse(report.contains("Date.month((birthday"), report);
    }
}
