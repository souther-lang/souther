package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total one comparison holds against every row of a table is owed, in place of the classes of
 * the positions it is made of, a row showing the weight of each position: a row on a border of the
 * total with that position alone away from the least it holds.
 */
class ATotalLookedUpInATableIsOwedAWeightForEachPositionTest {

    private static final String SOURCE = """
            module demo

            data N = { v: Int }
                invariant v >= 0
            data Row = { grade: Int, lowerBound: Int }
            let table: List<Row> = [ Row { grade = 2, lowerBound = 100 },
                                     Row { grade = 3, lowerBound = 200 } ]
            let gradeOf (m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 1, table)

            behavior f : (a: N, b: N) -> Int

            let f (a, b) =
                gradeOf(a.v + b.v)
            """;

    private static final String EXAMPLES = """

            example f
            """;

    private static final String ROW_OFF_EVERY_BORDER = """
                | (N { v = 1 }, N { v = 1 }) -> 1
            """;

    private static final String ROW_AT_A = """
                | (N { v = 100 }, N { v = 0 }) -> 2
            """;

    private static final String ROW_AT_B = """
                | (N { v = 0 }, N { v = 100 }) -> 2
            """;

    private static final String ROW_AT_BOTH = """
                | (N { v = 60 }, N { v = 40 }) -> 2
            """;

    private static final String SAID = "no row fixes how";

    @Test
    void everyPositionIsOwedItsWeightWhereNoRowIsOnABorder() {
        String report = reportOf(SOURCE + EXAMPLES + ROW_OFF_EVERY_BORDER);
        assertTrue(report.contains(SAID + " `a.v` weighs"), report);
        assertTrue(report.contains(SAID + " `b.v` weighs"), report);
    }

    @Test
    void aRowOnTheBorderWithOnePositionAwayShowsThatPositionAndNoOther() {
        String report = reportOf(SOURCE + EXAMPLES + ROW_OFF_EVERY_BORDER + ROW_AT_A);
        assertFalse(report.contains(SAID + " `a.v` weighs"), report);
        assertTrue(report.contains(SAID + " `b.v` weighs"), report);
    }

    @Test
    void aRowForEachPositionShowsThemAll() {
        String report = reportOf(SOURCE + EXAMPLES + ROW_OFF_EVERY_BORDER + ROW_AT_A + ROW_AT_B);
        assertFalse(report.contains(SAID), report);
    }

    /** A row on the border with both positions away from their least is about the sum of their
     *  weights and about neither of them. */
    @Test
    void aRowWithSeveralPositionsAwayShowsNone() {
        String report = reportOf(SOURCE + EXAMPLES + ROW_OFF_EVERY_BORDER + ROW_AT_BOTH);
        assertTrue(report.contains(SAID + " `a.v` weighs"), report);
        assertTrue(report.contains(SAID + " `b.v` weighs"), report);
    }

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
