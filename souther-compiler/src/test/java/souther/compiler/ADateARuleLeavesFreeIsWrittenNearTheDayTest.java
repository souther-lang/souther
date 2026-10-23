package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.time.LocalDate;
import java.time.Year;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

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

    /** The block of rows offered for the module. */
    private static String block(Compilation compilation) {
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule("m"));
        assertNotNull(offering, "the model under test compiles");
        return GeneratedRows.of(offering, Map.of(),
                SourceRendering.namedByIdentity(compilation.texts()), compilation.db()).text();
    }

    /** The dates of each row the block offers, in the order the row writes them. */
    private static List<List<LocalDate>> rows(Compilation compilation) {
        String block = block(compilation);
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

    /** A month and a day with no year are met in the year nearest the day's that has them, the
     *  later where two are as near: 2028 on a day of 2026, 2040 on a day of 2041. */
    @Test
    void aMonthAndADayAreMetFromTheDaysYear() {
        String source = source("d: Date", "d", "Date.month(d) == 2 && Date.day(d) == 29");
        for (LocalDate day : DAYS) {
            LocalDate expected = LocalDate.of(nearestLeapYear(day.getYear()), 2, 29);
            List<List<LocalDate>> rows = rows(source, day);
            assertTrue(rows.contains(List.of(expected)), "on " + day + ": " + rows);
            for (List<LocalDate> row : rows) {
                assertTrue(row.get(0).getYear() == day.getYear() || row.get(0).equals(expected),
                        "on " + day + ": " + row);
            }
        }
    }

    /** The nearest year is looked for from the day's own outward, so a day in the calendar's
     *  last year meets the last day of a year in that year and not centuries before it, and a day
     *  in its first year meets the first day of a year in that year and not centuries after. */
    @Test
    void aMonthAndADayAreMetInTheDaysYearAtTheEndsOfTheCalendar() {
        LocalDate last = LocalDate.MAX.minusMonths(6);
        List<List<LocalDate>> atTheEnd = rows(
                source("d: Date", "d", "Date.month(d) == 12 && Date.day(d) == 31"), last);
        assertTrue(atTheEnd.contains(List.of(LocalDate.MAX)), "on " + last + ": " + atTheEnd);
        LocalDate first = LocalDate.MIN.plusMonths(6);
        List<List<LocalDate>> atTheStart = rows(
                source("d: Date", "d", "Date.month(d) == 1 && Date.day(d) == 1"), first);
        assertTrue(atTheStart.contains(List.of(LocalDate.MIN)), "on " + first + ": " + atTheStart);
    }

    /** Of each finding, what it is owed for and how it is classed: its subject, its kind, the
     *  obligation it is about, what weakens it, what is left open and, for a point of a line, what
     *  covers it. */
    private static List<List<Object>> owed(List<Adequacy.Finding> findings) {
        List<List<Object>> out = new ArrayList<>();
        for (Adequacy.Finding each : findings) {
            List<Object> parts = new ArrayList<>(List.of(each.subject(), each.kind(),
                    each.weakenedBy(), each.open()));
            if (each.about() instanceof About.OfAnObligation obligation) {
                parts.add(obligation.obligationIdentity());
            }
            if (each.about() instanceof About.ABorderObligation border) {
                parts.add(border.role());
                parts.add(border.item().coverage());
                parts.add(border.item().open());
            }
            out.add(parts);
        }
        return out;
    }

    private static int nearestLeapYear(int from) {
        for (int away = 0; ; away++) {
            if (Year.isLeap(from + away)) {
                return from + away;
            }
            if (Year.isLeap(from - away)) {
                return from - away;
            }
        }
    }

    /** A year bounded below and a twenty-ninth of February are met in the leap year nearest the
     *  day that the bound leaves — the later where two are as near, as on a day of 2042, between
     *  2040 and 2044. */
    @Test
    void aBoundedYearWithAMonthAndADayIsTheNearestOneThatHasThem() {
        String source = source("d: Date", "d",
                "Date.year(d) >= 2030 && Date.month(d) == 2 && Date.day(d) == 29");
        List<LocalDate> days = new ArrayList<>(DAYS);
        days.add(LocalDate.of(2042, 3, 5));
        for (LocalDate day : days) {
            int leap = IntStream.rangeClosed(2030, day.getYear() + 8).filter(Year::isLeap).boxed()
                    .min(Comparator.comparingInt((Integer year) -> Math.abs(year - day.getYear()))
                            .thenComparing(Comparator.reverseOrder()))
                    .orElseThrow();
            List<List<LocalDate>> rows = rows(source, day);
            assertTrue(rows.contains(List.of(LocalDate.of(leap, 2, 29))),
                    "on " + day + ": " + rows);
        }
    }

    /** A value other than the one a rule singles out is near the day, and not beside the value:
     *  a date other than one in 2300, a date-time other than one, and a year other than one. */
    @Test
    void whatARuleSinglesOutLeavesTheRestNearTheDay() {
        for (LocalDate day : DAYS) {
            List<List<LocalDate>> other = rows(source("d: Date", "d",
                    "d == Date(\"2300-01-01\")"), day);
            assertTrue(other.contains(List.of(day)), "on " + day + ": " + other);
            assertTrue(other.stream().allMatch(row -> row.getFirst().equals(day)
                            || Math.abs(row.getFirst().getYear() - 2300) <= 1),
                    "every row is the day or beside the value, on " + day + ": " + other);
            String moments = block(measured(source("t: DateTime", "t",
                    "t == DateTime(\"2300-01-01T00:00:00\")"), day));
            assertTrue(moments.contains("DateTime(\"" + day.atStartOfDay() + ":00\")"),
                    "on " + day + ":\n" + moments);
            List<List<LocalDate>> years = rows(source("d: Date", "d", "Date.year(d) == 2300"), day);
            assertTrue(years.contains(List.of(day.withDayOfYear(1))), "on " + day + ": " + years);
        }
    }

    /** The case the issue was raised over: a year other than the one a rule names, beside a month
     *  it names, is the month in the day's year — and not the first year the calendar has. */
    @Test
    void aYearOtherThanTheOneNamedBesideANamedMonthIsThatMonthInTheDaysYear() {
        String source = source("d: Date", "d", "Date.year(d) == 2031 && Date.month(d) == 3");
        for (LocalDate day : DAYS) {
            List<List<LocalDate>> rows = rows(source, day);
            assertTrue(rows.contains(List.of(LocalDate.of(day.getYear(), 3, 1))),
                    "on " + day + ": " + rows);
            assertTrue(rows.stream().allMatch(row -> Math.abs(row.getFirst().getYear() - 2031) <= 2
                            || row.getFirst().getYear() == day.getYear()),
                    "on " + day + ": " + rows);
        }
    }

    /** Elements a rule bounds above, before the day, are the bound and the days before it: a
     *  collection of them holds as many as it is asked to, and not the one nearest the day. */
    @Test
    void elementsBoundedBeforeTheDayAreSteppedDownFromTheBound() {
        String source = """
                module m

                data Past = Date
                    invariant value <= Date("2020-12-31")

                behavior f : (s: Set<Past>) -> Bool
                let f (s) = if Set.size(s) >= 3 then true else false
                """;
        for (LocalDate day : DAYS) {
            String expected = "[Past(Date(\"2020-12-31\")), Past(Date(\"2020-12-30\")),"
                    + " Past(Date(\"2020-12-29\"))]";
            String block = block(measured(source, day));
            assertTrue(block.contains(expected), "on " + day + ":\n" + block);
        }
    }

    /** Elements nothing bounds are the day and the days either side of it, the day after before
     *  the day before, as every walk outward from a place takes them. */
    @Test
    void elementsNothingBoundsAreTheDayAndTheDaysEitherSideOfIt() {
        String source = source("s: Set<Date>", "s", "Set.size(s) >= 3");
        for (LocalDate day : DAYS) {
            List<List<LocalDate>> rows = rows(source, day);
            assertTrue(rows.contains(List.of(day, day.plusDays(1), day.minusDays(1))),
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

    /** A date-time and a moment nothing fixes are the start of the day, the moment in UTC; and
     *  one a rule bounds on one side is the start of the day where that side leaves it. */
    @Test
    void aDateTimeAndAMomentNothingFixesAreTheStartOfTheDay() {
        String source = """
                module m

                behavior f : (at: DateTime, when: Instant, after: DateTime, n: Int) -> Bool
                let f (at, when, after, n) =
                    if n >= 3 && after >= DateTime("2000-01-01T00:00:00") then true else false
                """;
        for (LocalDate day : DAYS) {
            String block = block(measured(source, day));
            String start = day.atStartOfDay().toString() + ":00";
            assertTrue(block.contains("DateTime(\"" + start + "\")"), "on " + day + ":\n" + block);
            assertTrue(block.contains("Instant(\"" + start + "Z\")"), "on " + day + ":\n" + block);
            assertFalse(block.contains("1970"), "on " + day + ":\n" + block);
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
     *  worked out on the first day is not what the second is answered with. And what the model
     *  owes, measured again on the same compilation, is what it owed the day before. */
    @Test
    void anotherDayIsAnsweredOnThatDay() {
        String source = """
                module m

                behavior f : (on: Date, birthday: Date) -> Bool
                let f (on, birthday) =
                    if Date.year(on) - Date.year(birthday) >= 40 then true else false

                example f
                    | (Date("2020-02-29"), Date("1990-05-01")) -> false
                """;
        Compilation compilation = measured(source, DAYS.get(0));
        List<List<LocalDate>> first = rows(compilation);
        AdequacyReport owedFirst = AdequacyReport.of(compilation);
        String saidFirst = owedFirst.human(SourceRendering.namedByIdentity(compilation.texts()));
        compilation.writtenOn(DAYS.get(1));
        List<List<LocalDate>> second = rows(compilation);
        AdequacyReport owedSecond = AdequacyReport.of(compilation);
        String saidSecond = owedSecond.human(SourceRendering.namedByIdentity(compilation.texts()));
        assertEquals(rows(source, DAYS.get(1)), second);
        assertFalse(first.equals(second), "the two days are years apart: " + first);
        // What is owed, as the values the report is made of and not only as it reads: the same
        // obligations, each classed the same way, and the same verdict. The rows a search found
        // for each are written on the day, and are what the first assertions above are about.
        assertFalse(owedFirst.findings().isEmpty(), "the model owes rows");
        assertEquals(owed(owedFirst.findings()), owed(owedSecond.findings()));
        assertEquals(owed(owedFirst.adequacyGaps()), owed(owedSecond.adequacyGaps()));
        assertEquals(owedFirst.adequacy(), owedSecond.adequacy());
        assertEquals(owed(owedFirst.assessment().gaps()), owed(owedSecond.assessment().gaps()));
        assertEquals(owedFirst.assessment().uncertainties(),
                owedSecond.assessment().uncertainties());
        assertEquals(saidFirst, saidSecond);
    }
}
