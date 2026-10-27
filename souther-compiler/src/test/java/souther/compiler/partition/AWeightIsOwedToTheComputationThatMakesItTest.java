package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row shows of the weights of a value derived from several positions is shown of the
 * computation that makes it, and by what the row's values fix of those weights.
 *
 * <p>The computation is the comparison a call of a helper reads: the same comparison read at two
 * calls is two computations, each of which can weigh its positions wrongly on its own. And a row
 * shows a weight by what the rows on the borders determine, which is not the same as one position
 * having moved: rows that each move several positions can fix every weight between them.
 */
class AWeightIsOwedToTheComputationThatMakesItTest {

    private static final String TABLE = """
            data Row = { grade: Int, lowerBound: Int }
            let table: List<Row> = [ Row { grade = 2, lowerBound = 100 },
                                     Row { grade = 3, lowerBound = 200 } ]
            let gradeOf (m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 1, table)
            """;

    private static final String SAID = "no row fixes how";

    /** The same comparison, read at two calls with two values: a row on a border of one is on no
     *  border of the other, and shows its weights only there. */
    @Test
    void theSameComparisonAtTwoCallsIsTwoComputations() {
        String report = reportOf("""
                module demo

                data N = { v: Int }
                    invariant v >= 0
                """ + TABLE + """

                behavior f : (a: N, b: N) -> Int

                let f (a, b) =
                    gradeOf(a.v + b.v) + gradeOf(a.v + 3 * b.v)

                example f
                    | (N { v = 1 }, N { v = 1 }) -> 2
                    | (N { v = 100 }, N { v = 0 }) -> 4
                    | (N { v = 0 }, N { v = 100 }) -> 5
                    | (N { v = 99 }, N { v = 0 }) -> 2
                    | (N { v = 0 }, N { v = 99 }) -> 4
                """);
        assertFalse(report.contains(SAID + " `b.v` weighs into `a.v + b.v`"), report);
        assertTrue(report.contains(SAID + " `b.v` weighs into `a.v + 3 * b.v`"), report);
    }

    /** Three positions each between nought and one: no row has one position alone away from nought
     *  on a border, and three that each move two fix every weight. */
    @Test
    void rowsThatEachMoveSeveralPositionsCanFixEveryWeight() {
        String report = reportOf("""
                module demo

                data U = { v: Int }
                    invariant v >= 0 && v <= 1
                """ + """
                data Row = { grade: Int, lowerBound: Int }
                let table: List<Row> = [ Row { grade = 2, lowerBound = 2 },
                                         Row { grade = 3, lowerBound = 3 } ]
                let gradeOf (m: Int): Int =
                    List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 1, table)

                behavior f : (a: U, b: U, c: U) -> Int

                let f (a, b, c) =
                    gradeOf(a.v + b.v + c.v)

                example f
                    | (U { v = 0 }, U { v = 0 }, U { v = 0 }) -> 1
                    | (U { v = 1 }, U { v = 1 }, U { v = 0 }) -> 2
                    | (U { v = 1 }, U { v = 0 }, U { v = 1 }) -> 2
                    | (U { v = 0 }, U { v = 1 }, U { v = 1 }) -> 2
                """);
        assertFalse(report.contains(SAID), report);
    }

    /** A value that takes one position from another: a weight of minus one has no row with that
     *  position alone away from nought on a border, and rows on it fix the weights all the same. */
    @Test
    void aDifferenceOfPositionsHasItsWeightsFixedByRowsOnItsBorders() {
        String report = reportOf("""
                module demo

                data N = { v: Int }
                    invariant v >= 0
                """ + TABLE + """

                behavior f : (a: N, b: N) -> Int

                let f (a, b) =
                    gradeOf(2 * a.v - b.v)

                example f
                    | (N { v = 1 }, N { v = 0 }) -> 1
                    | (N { v = 50 }, N { v = 0 }) -> 2
                    | (N { v = 60 }, N { v = 20 }) -> 2
                    | (N { v = 50 }, N { v = 1 }) -> 1
                    | (N { v = 55 }, N { v = 11 }) -> 1
                """);
        assertFalse(report.contains(SAID), report);
    }

    private static final String BRANCHES = """
            module demo

            data N = { v: Int }
                invariant v >= 0
            """ + TABLE + """

            behavior f : (a: N, b: N, c: N) -> Int

            let f (a, b, c) =
                if c.v > 0 then gradeOf(a.v + b.v) else gradeOf(a.v + b.v)

            example f
                | (N { v = 1 }, N { v = 1 }, N { v = 1 }) -> 1
                | (N { v = 100 }, N { v = 0 }, N { v = 1 }) -> 2
                | (N { v = 0 }, N { v = 100 }, N { v = 1 }) -> 2
                | (N { v = 99 }, N { v = 0 }, N { v = 1 }) -> 1
                | (N { v = 0 }, N { v = 99 }, N { v = 1 }) -> 1
            """;

    /**
     * Two calls on exclusive branches cut at the same places: the rows on the borders of the call
     * the rows reach are on no border of the other, and a weight fixed for one is not fixed for the
     * computation. Cut at the same places is no proof the two take their value from one place.
     */
    @Test
    void callsOnExclusiveBranchesAreNotFixedByTheRowsOfOne() {
        String report = reportOf(BRANCHES);
        assertTrue(report.contains(SAID + " `a.v` weighs"), report);
        assertTrue(report.contains(SAID + " `b.v` weighs"), report);
    }

    /** The control: rows that reach both branches fix both. */
    @Test
    void rowsThatReachBothBranchesFixTheWeightsOfBoth() {
        String report = reportOf(BRANCHES + """
                | (N { v = 100 }, N { v = 0 }, N { v = 0 }) -> 2
                | (N { v = 0 }, N { v = 100 }, N { v = 0 }) -> 2
                | (N { v = 99 }, N { v = 0 }, N { v = 0 }) -> 1
                | (N { v = 0 }, N { v = 99 }, N { v = 0 }) -> 1
                """);
        assertFalse(report.contains(SAID), report);
    }

    /**
     * One row with two readings, one on the border and one off it: the numbers of the reading off
     * the border are no numbers at it, and fix nothing. The row writes a pair at each of two
     * elements, and a reading is one element standing.
     */
    @Test
    void aReadingOfARowAwayFromTheBorderIsNoEvidenceOfIt() {
        String report = reportOf("""
                module demo

                data N = { v: Int }
                    invariant v >= 0
                data P = { a: N, b: N }
                """ + TABLE + """

                behavior f : (ps: List<P>) -> List<Int>

                let f (ps) =
                    List.map(p -> gradeOf(p.a.v + p.b.v), ps)

                example f
                    | ([P { a = N { v = 1 }, b = N { v = 1 } }]) -> [1]
                    | ([P { a = N { v = 100 }, b = N { v = 0 } }, P { a = N { v = 0 }, b = N { v = 50 } }, P { a = N { v = 99 }, b = N { v = 0 } }]) -> [2, 1, 1]
                """);
        long said = report.lines().filter(line -> line.contains(SAID)).count();
        assertEquals(1L, said, report);
    }

    /**
     * A row that does not hold fixes no weight: its answer is not the model's, so what it stands on
     * is not evidence of the model. The row at (100, 0) answers what the model does not, and the
     * weight of `a.v`, which only it reaches, is not fixed.
     */
    @Test
    void aRowThatDoesNotHoldFixesNoWeight() {
        String report = reportOf("""
                module demo

                data N = { v: Int }
                    invariant v >= 0
                """ + TABLE + """

                behavior f : (a: N, b: N) -> Int

                let f (a, b) =
                    gradeOf(a.v + b.v)

                example f
                    | (N { v = 1 }, N { v = 1 }) -> 1
                    | (N { v = 100 }, N { v = 0 }) -> 3
                    | (N { v = 0 }, N { v = 100 }) -> 2
                    | (N { v = 99 }, N { v = 0 }) -> 1
                    | (N { v = 0 }, N { v = 99 }) -> 1
                """);
        assertTrue(report.contains(SAID + " `a.v` weighs"), report);
        assertFalse(report.contains(SAID + " `b.v` weighs"), report);
    }

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
