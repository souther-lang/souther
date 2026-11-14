package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a name came to, kept for another reading to take, is what reading the value again comes to:
 * the report of a body is the same with the answers kept and with every name read afresh.
 *
 * <p>Each body reads a chain of products by names, and then reads the names the way that is
 * hardest on a kept answer: a name twice, a name under the elements of a list, a name under a
 * choice, and a name whose value is told to a rule about what it leaves over. A body where nothing
 * was kept is no comparison, so each is held to have read fewer values of names with them kept.
 */
class WhatANameCameToKeptOrReadAgainIsTheSameReportTest {

    private static final int LINKS = 8;

    private static String chain() {
        StringBuilder lets = new StringBuilder();
        for (int i = 1; i <= LINKS; i++) {
            lets.append("  let a").append(i).append(" = ")
                    .append(i == 1 ? "n" : "a" + (i - 1)).append(" * m\n");
        }
        return lets.toString();
    }

    /** The same chain where each link is a block that binds a value it never reads and one it
     *  does, so the walk meets a binding whose body reads it and one whose body does not. */
    private static String blocks() {
        StringBuilder lets = new StringBuilder();
        for (int i = 1; i <= LINKS; i++) {
            String before = i == 1 ? "n" : "a" + (i - 1);
            lets.append("  let a").append(i).append(" = {\n")
                    .append("    let unread = ").append(before).append(" * ").append(before)
                    .append("\n    let t = ").append(before).append(" * m\n    t\n  }\n");
        }
        return lets.toString();
    }

    private static String model(String lets, String last) {
        return "module chain\n\n"
                + "behavior f : (n: Int, m: Int, s: String, xs: List<Int>) -> Bool\n\n"
                + "let f (n, m, s, xs) = {\n" + lets + "  " + last + "\n}\n";
    }

    /** Names that are no more than another name, so one value is reached by several names. */
    private static final String ALIASES = "let b = a" + LINKS + "\n  let c = a" + LINKS
            + "\n  let d = a" + (LINKS - 1) + "\n  ";

    private static final List<String> LASTS = List.of(
            "a" + LINKS + " == m",
            "a" + LINKS + " * a" + (LINKS - 1) + " == m",
            "a" + LINKS + " + a" + LINKS + " >= m",
            "if s == \"x\" then a" + LINKS + " == m else a" + (LINKS - 1) + " == n",
            "List.all(k -> a" + LINKS + " + k >= m, xs)",
            "List.all(k -> a" + (LINKS - 1) + " * k >= a" + LINKS + ", xs)",
            "Int.floorMod(a" + LINKS + ", 7) < 5",
            "Int.floorMod(a" + LINKS + " + a" + (LINKS - 1) + ", 7) < 5 && a" + LINKS + " > m");

    private static String reportOf(String source) {
        AdequacyReport report = AdequacyReport.of(
                ACompiledModel.measured(source, Adequacy.Asked.fullReport()));
        SourceRendering rendering = SourceRendering.namedByIdentity(SourceLayouts.NONE);
        return report.humanInEnglish(rendering) + "\n" + report.json(rendering);
    }

    private static long namesRead(String source, List<String> report, boolean keeping) {
        long[] counting = {0};
        AffineForms.NAMES_READ = counting;
        AffineForms.KEEPING_NAMES = keeping;
        try {
            report.add(reportOf(source));
        } finally {
            AffineForms.KEEPING_NAMES = true;
            AffineForms.NAMES_READ = null;
        }
        return counting[0];
    }

    private static void assertTheSameReport(String lets, String last) {
        String source = model(lets, last);
        List<String> reports = new ArrayList<>();
        long kept = namesRead(source, reports, true);
        long again = namesRead(source, reports, false);
        assertEquals(reports.get(1), reports.get(0), "the report of: " + last);
        assertTrue(kept < again, "something was kept in: " + last + " (" + kept + " of "
                + again + ")");
    }

    @Test
    void theReportIsTheSameWithTheNamesKeptAndWithEveryNameReadAgain() {
        for (String last : LASTS) {
            assertTheSameReport(chain(), last);
        }
    }

    /** Where a binding's body reads what it binds and where it does not, which the walk tells
     *  apart by the names it read on the way. */
    @Test
    void theReportIsTheSameWhereLinksBindValuesTheyReadAndValuesTheyDoNot() {
        for (String last : LASTS) {
            assertTheSameReport(blocks(), last);
        }
    }

    /**
     * Where one name is read under each element of a list written out: the environments the
     * elements stand in are alike in every way but the element, and a name kept by what the
     * environment looks like and not by which it is would give one element's answer to another.
     */
    @Test
    void theReportIsTheSameWhereOneNameIsReadUnderEachElementOfAListWrittenOut() {
        for (String weekday : List.of(
                "Int.floorMod(d, 7) >= 1 && Int.floorMod(d, 7) <= 5",
                "Int.floorMod(d - 1, 7) < 5")) {
            String source = """
                    module demo exposing (g)

                    let first (base: Int, h: Int): Int = Option.withDefault(base,
                        List.find(d -> WEEKDAY && Bool.not(d == h),
                            List.map(k -> base + k, [0, 1, 2])))

                    behavior g : (base: Int, h: Int) -> Bool
                    let g (base, h) = Bool.not(first(base, h) == base)
                    """.replace("WEEKDAY", weekday);
            List<String> reports = new ArrayList<>();
            namesRead(source, reports, true);
            namesRead(source, reports, false);
            assertEquals(reports.get(1), reports.get(0), "the report of: " + weekday);
        }
    }

    /** Where several names stand for one value, which a name kept is not keyed by. */
    @Test
    void theReportIsTheSameWhereSeveralNamesStandForOneValue() {
        for (String last : List.of("b * c == m", "b * d == m", "b + c >= d * m",
                "Int.floorMod(b + c, 7) < 5 && d > m",
                "List.all(k -> b * k >= c, xs)")) {
            assertTheSameReport(chain() + "  " + ALIASES, last);
        }
    }
}
