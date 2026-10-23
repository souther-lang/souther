package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.time.LocalDate;
import java.time.Year;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A date the rules leave free is written near the day the rows are written on, and a date they fix
 * stays where they fix it.
 *
 * <p>Each claim is put on two days years apart, with what the rows should hold worked out from the
 * day by {@code java.time}: a search that started from one fixed date would answer one of the two
 * and not the other. And the day moves nothing the rules owe: the report of one model is the same
 * on both days, and a compilation told another day writes the rows a compilation started on that
 * day writes.
 */
class ADateARuleLeavesFreeIsWrittenNearTheDayTest {

    private static final List<LocalDate> DAYS =
            List.of(TestDay.DATE, LocalDate.of(2041, 3, 5));

    private static final Pattern DATE = Pattern.compile("Date\\(\"([^\"]+)\"\\)");

    private static String source(String params, String names, String body) {
        return """
                module m

                behavior f : (%s) -> Bool
                let f (%s) = if %s then true else false
                """.formatted(params, names, body);
    }

    private static Compilation measured(String source, LocalDate day) {
        Compilation compilation = Compilation.ofSource(source, "Main").writtenOn(day);
        compilation.measure(Adequacy.Asked.fullReport());
        return compilation;
    }

    /** The dates of each row the block offers, in the order the row writes them. */
    private static List<List<LocalDate>> rows(Compilation compilation) {
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule("m"));
        assertNotNull(offering, "the model under test compiles");
        String block = GeneratedRows.of(offering, Map.of(),
                SourceRendering.namedByIdentity(compilation.texts()), compilation.db()).text();
        List<List<LocalDate>> out = new ArrayList<>();
        for (String line : block.lines().filter(each -> each.startsWith("    |")).toList()) {
            List<LocalDate> dates = new ArrayList<>();
            Matcher found = DATE.matcher(line);
            while (found.find()) {
                dates.add(LocalDate.parse(found.group(1)));
            }
            out.add(dates);
        }
        assertFalse(out.isEmpty(), "the block offers rows");
        return out;
    }

    private static List<List<LocalDate>> rows(String source, LocalDate day) {
        return rows(measured(source, day));
    }

    /** A difference of two years fixes neither year: the one taken away is the day's, and the
     *  other stands the difference away from it. */
    @Test
    void aDifferenceOfYearsStandsInTheDaysYear() {
        String source = source("on: Date, birthday: Date", "on, birthday",
                "Date.year(on) - Date.year(birthday) >= 40");
        for (LocalDate day : DAYS) {
            List<List<LocalDate>> rows = rows(source, day);
            for (List<LocalDate> row : rows) {
                assertEquals(day.getYear(), row.get(1).getYear(), "on " + day + ": " + row);
            }
            assertEquals(Set.of(38, 39, 40, 41), rows.stream()
                    .map(row -> row.get(0).getYear() - row.get(1).getYear())
                    .collect(Collectors.toSet()), "on " + day);
        }
    }

    /** A year bounded on one side only is written in the year nearest the day that the side
     *  leaves, and the line itself where the rule draws one. */
    @Test
    void aYearOpenOnOneSideIsWrittenNearestTheDay() {
        String source = source("d: Date", "d", "Date.year(d) >= 2030");
        for (LocalDate day : DAYS) {
            Set<Integer> years = rows(source, day).stream().map(row -> row.get(0).getYear())
                    .collect(Collectors.toSet());
            assertTrue(years.containsAll(Set.of(2029, 2030)), "on " + day + ": " + years);
            int nearestBelow = Math.min(day.getYear(), 2029);
            int nearestAbove = Math.max(day.getYear(), 2030);
            assertTrue(years.contains(nearestBelow) && years.contains(nearestAbove),
                    "on " + day + ": " + years);
            assertTrue(years.stream().allMatch(year -> Math.abs(year - day.getYear()) <= 10
                            || Math.abs(year - 2030) <= 2),
                    "no year is far from both the day and the line, on " + day + ": " + years);
        }
    }

    /** A month and a day with no year are met in the first year from the day's that has them. */
    @Test
    void aMonthAndADayAreMetFromTheDaysYear() {
        String source = source("d: Date", "d", "Date.month(d) == 2 && Date.day(d) == 29");
        for (LocalDate day : DAYS) {
            int leap = day.getYear();
            while (!Year.isLeap(leap)) {
                leap++;
            }
            LocalDate expected = LocalDate.of(leap, 2, 29);
            List<List<LocalDate>> rows = rows(source, day);
            assertTrue(rows.contains(List.of(expected)), "on " + day + ": " + rows);
            for (List<LocalDate> row : rows) {
                assertTrue(row.get(0).getYear() == day.getYear() || row.get(0).equals(expected),
                        "on " + day + ": " + row);
            }
        }
    }

    /** A year bounded below and a twenty-ninth of February are met in the leap year nearest the
     *  day that the bound leaves — above the day before below it where two are as near. */
    @Test
    void aBoundedYearWithAMonthAndADayIsTheNearestOneThatHasThem() {
        String source = source("d: Date", "d",
                "Date.year(d) >= 2030 && Date.month(d) == 2 && Date.day(d) == 29");
        for (LocalDate day : DAYS) {
            int from = Math.max(day.getYear(), 2030);
            int leap = -1;
            for (int away = 0; leap < 0; away++) {
                for (int year : new int[] {from + away, from - away - 1}) {
                    if (leap < 0 && year >= 2030 && Year.isLeap(year)) {
                        leap = year;
                    }
                }
            }
            List<List<LocalDate>> rows = rows(source, day);
            assertTrue(rows.contains(List.of(LocalDate.of(leap, 2, 29))),
                    "on " + day + ": " + rows);
        }
    }

    /** A date the calendar does not have is no row, whatever the day. */
    @Test
    void aDateTheCalendarDoesNotHaveIsNoRow() {
        String source = source("d: Date", "d",
                "Date.year(d) == 2031 && Date.month(d) == 2 && Date.day(d) == 29");
        for (LocalDate day : DAYS) {
            for (List<LocalDate> row : rows(source, day)) {
                assertFalse(row.get(0).getYear() == 2031 && row.get(0).getMonthValue() == 2
                        && row.get(0).getDayOfMonth() == 29, "on " + day + ": " + row);
            }
        }
    }

    /** A date no rule reads, and the later of two dates only a count of days between them is
     *  asked of, are the day itself. */
    @Test
    void aDateNothingFixesIsTheDay() {
        String unread = source("a: Date, n: Int", "a, n", "n >= 3");
        String between = source("a: Date, b: Date", "a, b", "Date.daysBetween(a, b) >= 30");
        for (LocalDate day : DAYS) {
            for (List<LocalDate> row : rows(unread, day)) {
                assertEquals(List.of(day), row, "on " + day);
            }
            for (List<LocalDate> row : rows(between, day)) {
                assertEquals(day, row.get(1), "on " + day + ": " + row);
            }
        }
    }

    /** What a model owes does not turn on the day: its report is the same on both. */
    @Test
    void theDayMovesNothingTheRulesOwe() {
        String source = """
                module m

                behavior f : (on: Date, birthday: Date) -> Bool
                let f (on, birthday) =
                    if Date.year(on) - Date.year(birthday) >= 40 then true
                    else if Date.month(on) == 2 && Date.day(on) == 29 then true
                    else false

                example f
                    | (Date("2020-02-29"), Date("1990-05-01")) -> true
                    | (Date("2030-06-01"), Date("1990-05-01")) -> true
                """;
        List<String> reports = DAYS.stream().map(day -> {
            Compilation compilation = measured(source, day);
            return AdequacyReport.of(compilation)
                    .human(SourceRendering.namedByIdentity(compilation.texts()));
        }).toList();
        assertEquals(reports.get(0), reports.get(1));
    }

    /** A compilation told another day writes the rows one started on that day writes: what was
     *  worked out on the first day is not what the second is answered with. */
    @Test
    void anotherDayIsAnsweredOnThatDay() {
        String source = source("on: Date, birthday: Date", "on, birthday",
                "Date.year(on) - Date.year(birthday) >= 40");
        Compilation compilation = measured(source, DAYS.get(0));
        List<List<LocalDate>> first = rows(compilation);
        compilation.writtenOn(DAYS.get(1));
        List<List<LocalDate>> second = rows(compilation);
        assertEquals(rows(source, DAYS.get(1)), second);
        assertFalse(first.equals(second), "the two days are years apart: " + first);
    }
}
