package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.time.LocalDate;
import java.time.Year;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of the year of a date made from the input is read as the comparison of that date
 * with where the year begins.
 *
 * <p>{@code Date.year(Date.addDays(1, b)) >= 2027} holds where {@code Date.addDays(1, b)} is on or
 * after the first of January 2027, which is where {@code b} is on or after the thirty-first of
 * December before it.
 *
 * <p>The lines are held to what the program computes in two steps that can each fail alone. A row
 * is put on each side of every line the date arithmetic gives, and the compile runs it, so a row
 * whose answer the program does not give is an error. And the report is asked whether each of
 * those rows is the point the reading says it is, so a line the reading drew a day away leaves
 * the point with no row. The expected answers are worked out with {@code java.time} and not with
 * the reading's own arithmetic.
 */
class AYearOfAShiftedDateIsReadAsTheDatesItSpansTest {

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

    private static String about(String comparison) {
        return report(compiled("""
                module m

                behavior f : (b: Date) -> Bool
                let f (b) = %s
                """.formatted(comparison)));
    }

    private static boolean holds(LocalDate date, int shift, String relation, long year) {
        long found = date.plusDays(shift).getYear();
        return switch (relation) {
            case ">=" -> found >= year;
            case ">" -> found > year;
            case "<=" -> found <= year;
            case "<" -> found < year;
            case "==" -> found == year;
            default -> found != year;
        };
    }

    /** The dates the comparison turns over at: where the year it is made against begins. */
    private static List<LocalDate> linesOf(String relation, long year, int shift) {
        List<LocalDate> lines = new ArrayList<>();
        if (!relation.equals(">") && !relation.equals("<=")) {
            lineAt(lines, year, shift);
        }
        if (!relation.equals(">=") && !relation.equals("<")) {
            lineAt(lines, year + 1, shift);
        }
        return lines;
    }

    /** The line where {@code year} begins, where the shift leaves a date there to be one. */
    private static void lineAt(List<LocalDate> lines, long year, int shift) {
        if (year > Year.MAX_VALUE) {
            return;
        }
        try {
            lines.add(LocalDate.of((int) year, 1, 1).minusDays(shift));
        } catch (java.time.DateTimeException beyondTheRange) {
            // No date turns over there.
        }
    }

    /**
     * A row on each side of each line, and one well inside each of the classes they make — only
     * the dates the shift can be made of, since the program aborts on the others and a row that
     * aborts says nothing about a line.
     */
    private static Set<LocalDate> datesAround(List<LocalDate> lines, int shift) {
        Set<LocalDate> dates = new LinkedHashSet<>();
        for (LocalDate line : lines) {
            for (int away : new int[] {-400, -1, 0, 1, 400}) {
                try {
                    LocalDate date = line.plusDays(away);
                    date.plusDays(shift);
                    dates.add(date);
                } catch (java.time.DateTimeException beyondTheRange) {
                    // No such date, so no such row.
                }
            }
        }
        return dates;
    }

    private static String source(String comparison, int shift, String relation, long year,
                                 Set<LocalDate> dates) {
        StringBuilder rows = new StringBuilder();
        for (LocalDate date : dates) {
            rows.append("    | (Date(\"").append(date).append("\")) -> ")
                    .append(holds(date, shift, relation, year)).append('\n');
        }
        return """
                module m

                behavior f : (b: Date) -> Bool
                let f (b) = %s
                %s
                """.formatted(comparison, dates.isEmpty() ? "" : "\nexample f\n" + rows);
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
    void theYearOnTheLeftOfTheOperatorReadsTheSameAsOnTheRight() {
        String written = about("Date.year(Date.addDays(1, b)) >= 2027");
        String turned = about("2027 <= Date.year(Date.addDays(1, b))");

        assertEquals(borderLines(written), borderLines(turned), turned);
        assertTrue(turned.contains("measurement: complete"), turned);
    }

    @Test
    void anEqualityIsTheDatesOfTheYearAndSoDrawsBothEnds() {
        String report = about("Date.year(Date.addDays(1, b)) == 2027");

        assertTrue(report.contains("borders 2"), report);
        assertTrue(report.contains("= 2026-12-31"), report);
        assertTrue(report.contains("= 2027-12-31"), report);
    }

    @Test
    void everyRelationHoldsAtEachLineAndOnBothSidesOfIt() {
        long[] years = {1, 2024, 2027, 9999, 20000, Year.MAX_VALUE};
        int[] shifts = {1, -1, 30, -366};
        for (String relation : RELATIONS) {
            for (long year : years) {
                for (int shift : shifts) {
                    List<LocalDate> lines = linesOf(relation, year, shift);
                    String comparison = "Date.year(Date.addDays(%d, b)) %s %d"
                            .formatted(shift, relation, year);
                    Compilation compilation = compiled(source(comparison, shift, relation, year,
                            datesAround(lines, shift)));
                    String report = report(compilation);
                    String where = comparison + "\n" + report;

                    assertEquals(0, compilation.errors().size(), where);
                    assertTrue(report.contains("measurement: complete"), where);
                    assertFalse(report.contains("no row is at the ON point"), where);
                    assertFalse(report.contains("no row is at the OFF point"), where);
                }
            }
        }
    }

    @Test
    void aLeapDayDoesNotMoveTheLine() {
        // 2024 is a leap year, so the thirty-first of December 2023 plus a year of days is not the
        // thirty-first of December 2024.
        for (int shift : new int[] {366, -366, 365}) {
            Set<LocalDate> dates = new LinkedHashSet<>();
            for (LocalDate each : List.of(LocalDate.of(2023, 12, 31), LocalDate.of(2024, 2, 29),
                    LocalDate.of(2024, 12, 31), LocalDate.of(2025, 1, 1))) {
                dates.add(each.minusDays(1));
                dates.add(each);
                dates.add(each.plusDays(1));
            }
            String comparison = "Date.year(Date.addDays(%d, b)) >= 2025".formatted(shift);
            Compilation compilation = compiled(source(comparison, shift, ">=", 2025, dates));

            assertEquals(0, compilation.errors().size(), comparison + "\n" + report(compilation));
        }
    }

    @Test
    void aYearNoDateHasIsTheSameForEveryDate() {
        for (String comparison : List.of(
                "Date.year(Date.addDays(1, b)) >= 1000000000",
                "Date.year(Date.addDays(1, b)) > 999999999",
                "Date.year(Date.addDays(1, b)) < -1000000000",
                "Date.year(Date.addDays(1, b)) == 1000000000")) {
            String report = about(comparison);

            assertFalse(report.contains("not read"), comparison + "\n" + report);
            assertFalse(report.contains("read as f/b"), comparison + "\n" + report);
        }
    }

    @Test
    void aYearEveryDateIsOnOrAfterIsTrueOfEveryDate() {
        Compilation compilation = compiled("""
                module m

                behavior f : (b: Date) -> Bool
                let f (b) = Date.year(Date.addDays(1, b)) >= -1000000000

                example f
                    | (Date("2026-12-31")) -> true
                    | (Date("-999999999-01-02")) -> true
                """);

        assertEquals(0, compilation.errors().size(), report(compilation));
    }

    @Test
    void aShiftOffTheEndOfTheRangeAbortsAndIsNoRowThatReachedALine() {
        Compilation past = compiled("""
                module m

                behavior f : (b: Date) -> Bool
                let f (b) = Date.year(Date.addDays(1, b)) >= 999999999

                example f
                    | (Date("+999999999-12-31")) -> true
                """);

        assertEquals(1, past.errors().size(), "the program aborts there: " + report(past));

        Compilation near = compiled("""
                module m

                behavior f : (b: Date) -> Bool
                let f (b) = Date.year(Date.addDays(1, b)) >= 999999999

                example f
                    | (Date("+999999998-12-31")) -> true
                """);
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(near.db(), OfferingRequest.overTheModule("m")), Map.of(),
                SourceRendering.namedByIdentity(near.texts()), near.db()).text();

        assertFalse(offered.contains("+999999999-12-31"),
                "no row is offered at the date whose shift aborts: " + offered);
    }

    @Test
    void aLineBeyondTheLastDateIsReportedAndNotRefused() {
        Map<String, LocalDate> beginning = Map.of(
                "Date.year(Date.addDays(-366, b)) >= 999999999", LocalDate.of(999999999, 1, 1),
                "Date.addDays(-366, b) >= Date(\"+999999999-06-01\")",
                LocalDate.of(999999999, 6, 1));
        beginning.forEach((comparison, from) -> {
            String report = about(comparison);
            String past = "day " + (from.toEpochDay() + 366);

            assertTrue(report.contains("measurement: complete"), comparison + "\n" + report);
            assertTrue(report.contains(past), past + "\n" + comparison + "\n" + report);
        });
    }

    @Test
    void aPartOfADateThatRepeatsEveryYearIsNotOneLine() {
        String report = about("Date.month(Date.addDays(1, b)) >= 3");

        assertTrue(report.contains("not read"), report);
        assertFalse(report.contains("measurement: complete"), report);
    }

    @Test
    void theYearOfADateThatIsAPositionKeepsItsOwnTerm() {
        String report = about("Date.year(b) >= 2027");

        assertTrue(report.contains("read as f/Date.year(b)"), report);
        assertFalse(report.contains("read as f/b"), report);
    }

    private static List<String> borderLines(String report) {
        return report.lines().filter(line -> line.contains("read as f/b")).toList();
    }
}
