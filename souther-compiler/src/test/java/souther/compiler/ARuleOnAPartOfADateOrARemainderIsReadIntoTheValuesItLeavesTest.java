package souther.compiler;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule holding a part of the date at a position, or its remainder by a written divisor, at a value
 * is read into the values the position may hold — and is said to be read only where it was.
 *
 * <p>Two halves of one reading, and each without the other is wrong. Said to be read with the
 * values left as they were, a border asks for a row at the fifteenth of a month nobody can write a
 * value of the position at; with the values held and the rule left unaccounted, a reader is sent to
 * a clause that was carried out. So each model here is asked both: whether the rule stands, and what
 * the border made of the dates or numbers it does not leave.
 *
 * <p>Only what the values hold exactly. A remainder is held as the one class it leaves, so a rule
 * leaving it several numbers is not; a choice between two days is composed as the range they span,
 * which holds the days between, so it is not either. Both stand as they did.
 */
class ARuleOnAPartOfADateOrARemainderIsReadIntoTheValuesItLeavesTest {

    private static String reportOf(String type, String clause, String body, String rows) {
        Compilation compilation = Compilation.ofSource("""
                module probe.p

                data V = %s
                    invariant %s

                behavior f : (v: V) -> Bool

                let f (v) = %s

                example f
                %s
                """.formatted(type, clause, body, rows), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static List<String> standing(String report) {
        return report.lines().filter(line -> line.contains("not accounted for: invariant V"))
                .toList();
    }

    private static List<String> excluded(String report) {
        return report.lines().filter(line -> line.contains("excluded — no value can stand there"))
                .map(String::strip).toList();
    }

    /**
     * The first of each month: the rule is accounted for, and the two points beside a line drawn on
     * the fifteenth are dates no value is, so neither is owed a row and the rows that are written
     * cover the rest.
     *
     * <p>Written either way round, since which side the number is on is the author's spelling.
     */
    @Test
    void theFirstOfEachMonthIsReadAndTheDatesBetweenAreNoPointsOfTheBorder() {
        for (String clause : List.of("Date.day(value) == 1", "1 == Date.day(value)")) {
            String report = reportOf("Date", clause, "v.value > Date(\"2024-05-15\")", """
                        | "after" : (V(Date("2024-08-01"))) -> true
                        | "before" : (V(Date("2024-01-01"))) -> false""");

            assertEquals(List.of(), standing(report), clause + "\n" + report);
            assertEquals(List.of(
                            "· no ON point is owed at v = 2024-05-15 (comparison@null): excluded — no"
                                    + " value can stand there",
                            "· no OFF point is owed at v = 2024-05-15 (comparison@null): excluded — no"
                                    + " value can stand there"),
                    excluded(report), clause + "\n" + report);
            assertTrue(report.contains("adequacy: satisfied"), report);
        }
    }

    /**
     * Whole thousands, below nought as well: the remainder is a floor remainder, so minus five
     * thousand is one of them and minus five thousand five hundred and the number past it are not.
     */
    @Test
    void wholeThousandsAreReadOnBothSidesOfNought() {
        String report = reportOf("Int", "Int.floorMod(value, 1000) == 0", "v.value > -5500", """
                    | "a" : (V(0)) -> true
                    | "b" : (V(-9000)) -> false""");

        assertEquals(List.of(), standing(report), report);
        assertEquals(List.of(
                        "· no ON point is owed at v = -5500 (comparison@null): excluded — no value"
                                + " can stand there",
                        "· no OFF point is owed at v = -5500 (comparison@null): excluded — no value"
                                + " can stand there"),
                excluded(report), report);
    }

    /**
     * The last day of a month and the twenty-ninth of February, which only some months and some
     * years have: what is excluded is read off the calendar, so a line on the tenth of February is
     * no point either way and the rows at the dates that are cover the rest.
     */
    @Test
    void daysOnlySomeMonthsOrYearsHaveAreReadOffTheCalendar() {
        for (String[] each : List.of(
                new String[] {"Date.day(value) == 31", "2024-02-10",
                        "V(Date(\"2024-08-31\"))", "V(Date(\"2024-01-31\"))"},
                new String[] {"Date.day(value) == 29 && Date.month(value) == 2", "2025-01-01",
                        "V(Date(\"2032-02-29\"))", "V(Date(\"2020-02-29\"))"})) {
            String report = reportOf("Date", each[0], "v.value > Date(\"" + each[1] + "\")", """
                        | "after" : (%s) -> true
                        | "before" : (%s) -> false""".formatted(each[2], each[3]));

            assertEquals(List.of(), standing(report), each[0] + "\n" + report);
            assertEquals(2, excluded(report).size(), each[0] + "\n" + report);
            assertTrue(report.contains("adequacy: satisfied"), each[0] + "\n" + report);
        }
    }

    /**
     * A remainder left several numbers, and a choice between two days, stand as they did, in the
     * words they were told.
     *
     * <p>The control on the ones above. Each is read by the same reading of the numbers an
     * operation answers, and what it leaves the values is more than one class or a range holding
     * days neither branch names — taken in, it would be a rule nobody carried out said to be read.
     */
    @Test
    void whatTheValuesDoNotHoldExactlyStandsAsItDid() {
        assertEquals(List.of(
                        "      · not accounted for: invariant V #1 — which values may stand at v: it"
                                + " is about a value made from this one, and what it says about the"
                                + " values here is not worked out",
                        "      · not accounted for: invariant V #1 — whether the values stop on v:"
                                + " it is about a value made from this one, and what it says about"
                                + " the values here is not worked out"),
                standing(reportOf("Int", "Int.floorMod(value, 7) >= 3", "v.value > 10", """
                            | "a" : (V(12)) -> true
                            | "b" : (V(3)) -> false""")));
        assertEquals(List.of(
                        "      · not accounted for: invariant V #1 — which values may stand at v:"
                                + " written in a form this compiler does not read"),
                standing(reportOf("Date", "Date.day(value) == 1 || Date.day(value) == 15",
                        "v.value > Date(\"2024-05-10\")", """
                            | "a" : (V(Date("2024-06-01"))) -> true
                            | "b" : (V(Date("2024-01-01"))) -> false""")));
    }
}
