package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleRef;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;
import souther.compiler.types.WrittenOwner;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A bound on one date of an age comparison leaves the years of the other read: the years the
 * bound settles the comparison at, whatever the bounded date is, are a class of their own, and
 * every other year reaches both sides of it.
 *
 * <p>A birthday from 1900 on is never sixty at a day before 1960, so at each year of {@code on} up
 * to 1959 the comparison is false and from 1960 a birthday reaches either side. The line at 1960
 * is where the bound and the comparison meet, and no line the author wrote, so no row is owed at
 * it. The same is said of a date moved a day back, whose year starts at 1899, of a day bounded as
 * well, and of an age read through the months and the days of the dates.
 */
class AValueTheOtherDatesBoundSettlesIsAClassOfItsOwnTest {

    private static final String FROM_1900 = "birthday >= Date(\"1900-01-01\")";

    private static final String THE_YEARS = "Date.year(on) - Date.year(p.birthday)";

    private static final String THE_YEARS_A_DAY_BACK =
            "Date.year(on) - Date.year(Date.addDays(0 - 1, p.birthday))";

    private static final String MOVED = "Date.year((p.birthday -1 days))";

    private static Compilation compiled(String source) {
        return ACompiledModel.compiles(ACompiledModel.measured(source,
                Adequacy.Asked.fullReport()));
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /**
     * {@code source} compiled with no rows measured: what its rules divide each position into,
     * and what they leave unread, are derived all the same, and no row is searched for.
     */
    private static Compilation divided(String source) {
        return ACompiledModel.compiles(ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.OFF)));
    }

    /** The positions the reading of {@code ceiling} left something unread about. */
    private static List<String> unread(Compilation compilation) {
        return compilation.db().ask(new Adequacy.Coverage("d")).value().get("ceiling").notRead()
                .stream().map(PartitionEvidence.NotRead::at).toList();
    }

    /** What the reading of the comparisons written in {@code definition} left unread, as the
     *  position and the reason. */
    private static List<String> unreadOfTheComparisonsIn(Compilation compilation,
                                                         String definition) {
        return compilation.db().ask(new Adequacy.Coverage("d")).value().get("ceiling").notRead()
                .stream().filter(each -> each.cited().stream().anyMatch(cited ->
                        cited.rule() instanceof RuleRef.Comparison comparison
                                && comparison.origin().owner() instanceof WrittenOwner.Body body
                                && body.definition().equals(definition)))
                .map(each -> each.at() + " " + each.reason()).toList();
    }

    /** The classes of each axis of {@code ceiling}, by the axis. */
    private static Map<String, List<String>> classes(Compilation compilation) {
        Map<String, List<String>> out = new TreeMap<>();
        compilation.db().ask(new Adequacy.Coverage("d")).value().get("ceiling").axes()
                .forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    /** An age of sixty or a disability, of a person whose birthday {@code bound} holds, on a day
     *  of type {@code on}, the age being {@code years}. */
    private static String aged(String bound, String on, String years) {
        return """
                module d

                data Today = Date
                    invariant value >= Date("2000-01-01")
                data Century = Date
                    invariant value >= Date("2000-01-01") && value <= Date("2099-12-31")

                data P =
                    { birthday: Date
                    , disabled: Bool
                    }
                    invariant %s

                behavior ceiling : (p: P, on: %s) -> Int
                let ceiling (p, on) =
                    if %s >= 60 || p.disabled then 1800 else 1300
                """.formatted(bound, on, years);
    }

    @Test
    void theYearsOfTheOtherDateUpToWhereTheBoundSettlesTheComparisonAreAClass() {
        Compilation compilation = compiled(aged(FROM_1900, "Date", THE_YEARS));
        String report = report(compilation);

        assertTrue(report.contains("measurement: complete"), report);
        assertEquals(List.of("Date.year(on): -999999999 <= x <= 1959",
                "Date.year(on): 1959 < x <= 999999999"),
                classes(compilation).get("Date.year(on)"), report);
    }

    /** No row is owed at the line the bound draws: the comparison's own four points and the
     *  bound's own are all that is owed. */
    @Test
    void noRowIsOwedAtTheLineTheBoundAndTheComparisonDrawTogether() {
        String report = report(compiled(aged(FROM_1900, "Date", THE_YEARS)));

        assertTrue(report.contains("border      borders 3   obligations 0/4"), report);
        assertFalse(report.contains("1959"), report);
        assertFalse(report.contains("1960"), report);
    }

    @Test
    void theYearOfABirthdayADayBackStartsAYearEarlier() {
        Compilation compilation = compiled(aged(FROM_1900, "Date", THE_YEARS_A_DAY_BACK));
        String report = report(compilation);

        assertTrue(report.contains("measurement: complete"), report);
        assertEquals(List.of("Date.year(on): -999999999 <= x <= 1958",
                "Date.year(on): 1958 < x <= 999999999"),
                classes(compilation).get("Date.year(on)"), report);
    }

    /**
     * With the day from 2000 on, a birthday in a year up to 1940 is sixty at every day there is,
     * and every year of the day has a birthday on either side. So the birthday's years are parted
     * and the day's are not.
     */
    @Test
    void aBoundOnEachDateSettlesTheYearsOfTheOther() {
        Compilation compilation = compiled(aged(FROM_1900, "Today",
                "Date.year(on.value) - Date.year(Date.addDays(0 - 1, p.birthday))"));
        String report = report(compilation);

        assertTrue(report.contains("measurement: complete"), report);
        assertEquals(List.of(MOVED + ": 1899 <= x <= 1940", MOVED + ": 1940 < x < 999999940",
                MOVED + ": 999999940 <= x <= 999999999"), classes(compilation).get(MOVED), report);
        assertTrue(report.contains("rather than dividing the values here, about"
                + " `Date.year(on.value)`") || !classes(compilation).containsKey("Date.year(on)"),
                report);
    }

    /** And with both bounded above as well, a birthday from 2040 is under sixty at every day of
     *  the century, which is a class of the birthday's years too. */
    @Test
    void boundsAboveAsWellSettleTheLaterYearsToo() {
        Compilation compilation = compiled(aged(
                FROM_1900 + " && birthday <= Date(\"2099-12-31\")", "Century",
                "Date.year(on.value) - Date.year(Date.addDays(0 - 1, p.birthday))"));
        String report = report(compilation);

        assertTrue(report.contains("measurement: complete"), report);
        assertEquals(List.of(MOVED + ": 1899 <= x <= 1940", MOVED + ": 1940 < x < 2040",
                MOVED + ": 2040 <= x <= 2099"), classes(compilation).get(MOVED), report);
    }

    private static final String AGE_IN_MONTHS_AND_DAYS = """
            module d

            data P = { birthday: Date }
                invariant birthday >= Date("1900-01-01")

            let ageOn (birthday: Date, on: Date): Int =
                Date.year(on) - Date.year(birthday)
                    - (if Date.month(on) * 100 + Date.day(on)
                            < Date.month(birthday) * 100 + Date.day(birthday)
                       then 1 else 0)

            behavior ceiling : (p: P, on: Date) -> Bool
            let ceiling (p, on) =
                ageOn(Date.addDays(0 - 1, p.birthday), on) >= 40
            """;

    /** {@link #AGE_IN_MONTHS_AND_DAYS} measured, which the tests of it only read. */
    private static final class AnAge {
        static final Compilation MEASURED = compiled(AGE_IN_MONTHS_AND_DAYS);
    }

    @Test
    void anAgeReadThroughTheMonthsAndDaysOfABoundedBirthdayIsRead() {
        String report = report(AnAge.MEASURED);

        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("not worked out"), report);
    }

    /** The age the calendar gives the pair, and not the reading. */
    private static int ageAttained(LocalDate birthday, LocalDate on) {
        LocalDate dayBefore = birthday.minusDays(1);
        boolean beforeTheDay = on.getMonthValue() * 100 + on.getDayOfMonth()
                < dayBefore.getMonthValue() * 100 + dayBefore.getDayOfMonth();
        return on.getYear() - dayBefore.getYear() - (beforeTheDay ? 1 : 0);
    }

    /**
     * Each row offered is a birthday the bound holds, and is answered by the program as the
     * calendar works the age out: the rows are written as the examples, with the answer the
     * calendar gives, and an answer the program gives otherwise is an error. A row at each side of
     * each line of the age is among them, and no point is left without one.
     */
    @Test
    void theRowsOfferedAreBirthdaysTheBoundHoldsAndAnsweredAsTheCalendarWorksTheAgeOut() {
        Compilation offering = AnAge.MEASURED;
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(offering.db(), OfferingRequest.overTheModule("d")),
                Map.of(), SourceRendering.namedByIdentity(offering.texts()), offering.db())
                .textInEnglish();

        StringBuilder examples = new StringBuilder();
        Set<Integer> ages = new HashSet<>();
        for (String line : offered.lines().filter(each -> each.contains("Date(\"")).toList()) {
            List<LocalDate> dates = new ArrayList<>();
            int at = 0;
            while ((at = line.indexOf("Date(\"", at)) >= 0) {
                int end = line.indexOf('"', at + 6);
                dates.add(LocalDate.parse(line.substring(at + 6, end)));
                at = end;
            }
            LocalDate birthday = dates.get(0);
            LocalDate on = dates.get(1);
            assertFalse(birthday.isBefore(LocalDate.of(1900, 1, 1)), line);
            int age = ageAttained(birthday, on);
            ages.add(age);
            examples.append("    | (P { birthday = Date(\"").append(birthday)
                    .append("\") }, Date(\"").append(on).append("\")) -> ")
                    .append(age >= 40).append('\n');
        }
        assertTrue(ages.containsAll(List.of(39, 40)), ages + "\n" + offered);

        Compilation answered = ACompiledModel.measured(
                AGE_IN_MONTHS_AND_DAYS + "\nexample ceiling\n" + examples,
                Adequacy.Asked.fullReport());
        String report = report(answered);
        assertEquals(0, answered.errors().size(), report + "\n" + examples);
        assertFalse(report.contains("no row is at"), report);
    }

    /**
     * A comparison read again where the first reading of it decided the way: the comparison with
     * {@code r} asks {@code old}, which compares the age, and the answer asks it again. The second
     * reading is reached along a way that holds the age at sixty and ways that hold it under, and
     * no {@code on} before 1960 has a row along the first. Read once the ways have met, the values
     * up to 1959 fail it along every way that has a row at them: whole numbers no difference of
     * which passes where an {@code Int} stops, so that every row the runs hold is computed.
     */
    @Test
    void aComparisonReadAgainWhereTheFirstReadingDecidedTheWayIsReadOverWholeNumbers() {
        Compilation compilation = compiled("""
                module d

                data Day = Int
                    invariant value >= 0 && value <= 5000

                data P = { born: Int, disabled: Bool }
                    invariant born >= 1900 && born <= 3000

                let old (p: P, on: Day): Int =
                    if on.value - p.born >= 60 || p.disabled
                    then 1800 else 1300

                behavior ceiling : (p: P, on: Day, r: Int) -> Int
                let ceiling (p, on, r) =
                    if r >= old(p, on) then old(p, on) else 3
                """);
        String report = report(compilation);

        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("not worked out"), report);
    }

    /**
     * The same over dates. Along the way the first reading decided true, the year of {@code on}
     * is shown only from 1960, where a birthday from 1900 is sixty: the region holds the year of
     * the birthday where the birthday lies, so the years before have no row along it.
     */
    @Test
    void aComparisonOfYearsReadAgainIsReadOverTheYearsTheBoundLeaves() {
        Compilation compilation = compiled("""
                module d

                data P = { birthday: Date, disabled: Bool }
                    invariant birthday >= Date("1900-01-01")

                let old (p: P, on: Date): Int =
                    if Date.year(on) - Date.year(p.birthday) >= 60 || p.disabled
                    then 1800 else 1300

                behavior ceiling : (p: P, on: Date, r: Int) -> Int
                let ceiling (p, on, r) =
                    if r >= old(p, on) then old(p, on) else 3
                """);
        String report = report(compilation);

        assertTrue(report.contains("measurement: complete"), report);
        assertEquals(List.of(), unread(compilation));
        assertEquals(List.of("Date.year(on): -999999999 <= x <= 1959",
                "Date.year(on): 1959 < x <= 999999999"),
                classes(compilation).get("Date.year(on)"), report);
    }

    /**
     * An age worked out through the months, read again. The statements of months on each way
     * hold at some month in every year the dates may be in, so the years are read through the
     * statements of years alone.
     */
    @Test
    void anAgeThroughTheMonthsAndDaysReadAgainIsRead() {
        List<String> unread = unread(divided("""
                module d

                data P = { birthday: Date }
                    invariant birthday >= Date("1900-01-01")

                let old (p: P, on: Date): Int =
                    if Date.year(on) - Date.year(p.birthday)
                            - (if Date.month(on) < Date.month(p.birthday) then 1 else 0) >= 60
                    then 1800 else 1300

                behavior ceiling : (p: P, on: Date, r: Int) -> Int
                let ceiling (p, on, r) =
                    if r >= old(p, on) then old(p, on) else 3
                """));

        assertTrue(unread.stream().noneMatch(at -> at.startsWith("Date.year")), unread.toString());
    }

    /**
     * A comparison of months read again along ways that state a year of the same date. The
     * statement of the year holds in years every month is in, so the months are read through
     * the statements of months alone.
     */
    @Test
    void aComparisonOfMonthsReadAgainUnderAYearIsRead() {
        List<String> unread = unread(divided("""
                module d

                let old (on: Date, b: Date): Int =
                    if Date.month(on) - Date.month(b) >= 3 then 1800 else 1300

                behavior ceiling : (on: Date, b: Date, r: Int) -> Int
                let ceiling (on, b, r) =
                    if Date.year(on) >= 2000 then
                        (if r >= old(on, b) then old(on, b) else 3)
                    else 4
                """));

        assertTrue(unread.stream().noneMatch(at -> at.startsWith("Date.month")),
                unread.toString());
    }

    /**
     * A way whose statements no date meets shows no row. The comparison is read again only along
     * ways through the thirtieth of February, which the region holds as a month and a day it
     * leaves and no date is. Along the way that decided it true, the region leaves a birthday's
     * year up to sixty before the calendar's last, and those years are no row's: no class of the
     * birthday's years is made of them.
     */
    @Test
    void aYearAWaysMonthsAndDaysKeepFromEveryDateIsNoRowAlongIt() {
        Compilation compilation = divided("""
                module d

                data P = { birthday: Date }
                    invariant birthday >= Date("1900-01-01")

                let old (p: P, on: Date): Int =
                    if Date.year(on) - Date.year(p.birthday) >= 60 then 1800 else 1300

                behavior ceiling : (p: P, on: Date, r: Int) -> Int
                let ceiling (p, on, r) =
                    if Date.month(on) * 100 + Date.day(on) == 230 then
                        (if r >= old(p, on) then old(p, on) else 3)
                    else 4
                """);

        assertFalse(classes(compilation).containsKey("Date.year(p.birthday)"),
                classes(compilation).toString());
    }

    /** The comparison of ages read again along a way that also states {@code ofAnotherDate} of a
     *  date {@code d} nothing ties to the person or the day. */
    private static String readAgainBeside(String ofAnotherDate) {
        return """
                module d

                data P = { birthday: Date, disabled: Bool }
                    invariant birthday >= Date("1900-01-01")

                let old (p: P, on: Date): Int =
                    if Date.year(on) - Date.year(p.birthday) >= 60 || p.disabled
                    then 1800 else 1300

                behavior ceiling : (p: P, on: Date, d: Date, r: Int) -> Int
                let ceiling (p, on, d, r) =
                    if %s then
                        (if r >= old(p, on) then old(p, on) else 3)
                    else 4
                """.formatted(ofAnotherDate);
    }

    /**
     * A statement weighing the year and the month of another date, which February 2000 holds,
     * leaves the ages read again as they are read without it: some date holds it, and nothing
     * it says is of the person or the day.
     */
    @Test
    void aStatementOfTwoPartsOfAnotherDateThatSomeDateHoldsLeavesTheAgesRead() {
        List<String> unread = unread(divided(
                readAgainBeside("Date.year(d) * 100 + Date.month(d) == 200002")));

        assertTrue(unread.stream().noneMatch(at -> at.startsWith("Date.year(on)")
                || at.startsWith("Date.year(p.birthday)")), unread.toString());
    }

    /**
     * Statements of another date that no date holds, the thirtieth of February: no row comes
     * along the way, so the ages are not read off what the region leaves there. Read there,
     * they would be read of rows there are none of.
     */
    @Test
    void statementsOfAnotherDateThatNoDateHoldsLeaveTheAgesUnread() {
        List<String> unread = unread(divided(
                readAgainBeside("Date.month(d) == 2 && Date.day(d) == 30")));

        assertTrue(unread.containsAll(List.of("Date.year(on)", "Date.year(p.birthday)")),
                unread.toString());
    }

    /**
     * The day itself the twenty-ninth of February, which some date is: along the way the day's
     * year is a leap year, which the region does not hold, and the birthday is tied to the day by
     * the age the first reading decided. Each side is of a date the way names by two numbers and
     * ties to it, so neither is read off what the region leaves there.
     */
    @Test
    void aDateTheWayNamesByTwoNumbersAndTiesToTheSideLeavesTheSideUnread() {
        List<String> unread = unreadOfTheComparisonsIn(divided("""
                module d

                data P = { birthday: Date }

                let old (p: P, on: Date): Int =
                    if Date.year(on) - Date.year(p.birthday) >= 60 then 1800 else 1300

                behavior ceiling : (p: P, on: Date, r: Int) -> Int
                let ceiling (p, on, r) =
                    if Date.month(on) == 2 && Date.day(on) == 29 then
                        (if r >= old(p, on) then old(p, on) else 3)
                    else 4
                """), "old");

        assertTrue(unread.containsAll(List.of("Date.year(on) RULE_RELATING_TWO_VALUES",
                "Date.year(p.birthday) RULE_RELATING_TWO_VALUES")), unread.toString());
    }

    /** The same comparison over whole numbers, which is how the section reads it. */
    @Test
    void aBoundOnOneNumberSettlesTheOtherWhereItIsAWholeNumber() {
        Compilation compilation = compiled("""
                module d

                data P =
                    { born: Int
                    , disabled: Bool
                    }
                    invariant born >= 1900

                behavior ceiling : (p: P, on: Int) -> Int
                let ceiling (p, on) =
                    if on - p.born >= 60 || p.disabled then 1800 else 1300
                """);

        assertEquals(List.of("on: x <= 1959", "on: 1959 < x"), classes(compilation).get("on"),
                report(compilation));
    }
}
