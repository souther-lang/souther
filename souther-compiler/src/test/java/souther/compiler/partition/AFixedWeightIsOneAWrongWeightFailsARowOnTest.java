package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.function.IntBinaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the report calls a fixed weight is one a wrong weight is caught on.
 *
 * <p>The claim is about an implementation: that a computation weighing a position otherwise would
 * not agree with the rows. So the claim is held to it. For each way a threshold is written, rows
 * that the report calls enough are run against the model with a position dropped, and with it
 * weighed more, and each of those has to fail a row. Which side of the threshold catches which is
 * the comparison's — a strict one holds one value further up than a non-strict one — so rows on
 * both sides are what the report has to ask for.
 */
class AFixedWeightIsOneAWrongWeightFailsARowOnTest {

    /** A threshold written four ways, over the grades at 100 and at 200. */
    private enum Written {
        AT_OR_ABOVE("r.lowerBound <= m", (m, t) -> m >= t ? 1 : 0),
        ABOVE("r.lowerBound < m", (m, t) -> m > t ? 1 : 0),
        FLIPPED_AT_OR_ABOVE("m >= r.lowerBound", (m, t) -> m >= t ? 1 : 0),
        FLIPPED_ABOVE("m > r.lowerBound", (m, t) -> m > t ? 1 : 0);

        private final String condition;
        private final IntBinaryOperator reaches;

        Written(String condition, IntBinaryOperator reaches) {
            this.condition = condition;
            this.reaches = reaches;
        }

        /** The grade of a total: the last row of the table it reaches. */
        int gradeOf(int m) {
            int grade = 1;
            if (reaches.applyAsInt(m, 100) == 1) {
                grade = 2;
            }
            if (reaches.applyAsInt(m, 200) == 1) {
                grade = 3;
            }
            return grade;
        }
    }

    private static final String SAID = "no row fixes how";

    private static String source(Written written, String total, List<int[]> rows) {
        StringBuilder out = new StringBuilder("""
                module demo

                data N = { v: Int }
                    invariant v >= 0
                data Row = { grade: Int, lowerBound: Int }
                let table: List<Row> = [ Row { grade = 2, lowerBound = 100 },
                                         Row { grade = 3, lowerBound = 200 } ]
                let gradeOf (m: Int): Int =
                    List.fold((acc, r) -> if %s then r.grade else acc, 1, table)

                behavior f : (a: N, b: N) -> Int

                let f (a, b) =
                    gradeOf(%s)

                example f
                """.formatted(written.condition, total));
        for (int[] row : rows) {
            out.append("    | (N { v = %d }, N { v = %d }) -> %d%n".formatted(row[0], row[1],
                    written.gradeOf(row[0] + row[1])));
        }
        return out.toString();
    }

    /** Rows at the threshold and on each side of it, one position at a time, and one away from
     *  every border. Which of the three is where the comparison holds is the spelling's. */
    private static final List<int[]> ROWS = List.of(new int[] {1, 1},
            new int[] {99, 0}, new int[] {100, 0}, new int[] {101, 0},
            new int[] {0, 99}, new int[] {0, 100}, new int[] {0, 101});

    private static Compilation compile(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    @Test
    void rowsAtTheThresholdFixBothWeightsHoweverTheThresholdIsWritten() {
        for (Written written : Written.values()) {
            Compilation model = compile(source(written, "a.v + b.v", ROWS));
            assertEquals(List.of(), model.errors(), () -> written + ": the rows hold of the model");
            String report = AdequacyReport.of(model)
                    .human(SourceRendering.namedByIdentity(model.texts()));
            assertFalse(report.contains(SAID), () -> written + ": " + report);
        }
    }

    /** What the claim is for: weighing a position otherwise fails a row the report called enough. */
    @Test
    void aPositionWeighedOtherwiseFailsARowTheReportCalledEnough() {
        for (Written written : Written.values()) {
            for (String wrong : List.of("b.v", "a.v", "2 * a.v + b.v", "a.v + 2 * b.v")) {
                Compilation mutant = compile(source(written, wrong, ROWS));
                assertFalse(mutant.errors().isEmpty(), () -> written + ": `" + wrong
                        + "` passes every row the report called enough");
            }
        }
    }

    /** A control: rows away from the threshold fix nothing, and the report says so. */
    @Test
    void rowsNextToTheThresholdAreNotEnough() {
        for (Written written : Written.values()) {
            Compilation model = compile(source(written, "a.v + b.v",
                    List.of(new int[] {1, 1}, new int[] {99, 0}, new int[] {0, 99})));
            String report = AdequacyReport.of(model)
                    .human(SourceRendering.namedByIdentity(model.texts()));
            assertTrue(report.contains(SAID + " `a.v` weighs"), () -> written + ": " + report);
        }
    }
}
