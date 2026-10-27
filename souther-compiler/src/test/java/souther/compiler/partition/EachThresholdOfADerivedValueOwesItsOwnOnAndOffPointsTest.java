package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value computed from several positions and cut at several places owes its ON and OFF points once
 * for each place, so rows at the points of one threshold of a table say nothing of the next.
 */
class EachThresholdOfADerivedValueOwesItsOwnOnAndOffPointsTest {

    private static final String MISSING_ON = "no row is at the ON point";
    private static final String MISSING_OFF = "no row is at the OFF point";

    private static String table(int top) {
        return """
                module demo

                data N = { v: Int }
                    invariant v >= 0
                data Row = { grade: Int, lowerBound: Int }
                let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                         Row { grade = 2, lowerBound = 100 },
                                         Row { grade = 3, lowerBound = %d } ]
                let gradeOf (m: Int): Int =
                    List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 0, table)

                behavior f : (a: N, b: N) -> Int

                let f (a, b) =
                    gradeOf(a.v + b.v)

                """.formatted(top);
    }

    private static final String AT_100 = """
            example f
                | (N { v = 100 }, N { v = 0 }) -> 2
                | (N { v = 0 }, N { v = 100 }) -> 2
                | (N { v = 99 }, N { v = 0 }) -> 1
                | (N { v = 0 }, N { v = 99 }) -> 1
            """;

    private static final String AT_200 = """
                | (N { v = 200 }, N { v = 0 }) -> 3
                | (N { v = 0 }, N { v = 199 }) -> 2
            """;

    /** The points of the threshold 100 answered, and the points of the threshold 200 not. */
    @Test
    void aThresholdNoRowStandsAtIsAGapAndNamesItself() {
        String report = reportOf(table(200) + AT_100);
        assertTrue(report.contains(MISSING_ON), report);
        assertTrue(report.contains(MISSING_OFF), report);
        assertTrue(report.contains("= 200 in gradeOf"), report);
        assertTrue(report.contains("= 199 in gradeOf"), report);
        assertFalse(report.contains("= 100 in gradeOf"), report);
    }

    /** The same rows with the third bound written 2000 pass nothing more. */
    @Test
    void movingTheThirdBoundDoesNotChangeWhatTheRowsAtTheSecondShow() {
        String report = reportOf(table(2000) + AT_100);
        assertTrue(report.contains(MISSING_ON), report);
        assertTrue(report.contains("= 2000 in gradeOf"), report);
    }

    /** Rows at the points of every threshold leave no point of any of them owed. */
    @Test
    void rowsAtEveryThresholdLeaveNothingOwed() {
        String report = reportOf(table(200) + AT_100 + AT_200);
        assertFalse(report.contains(MISSING_ON), report);
        assertFalse(report.contains(MISSING_OFF), report);
    }

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
