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
 * <p>The claim is about an implementation: that a computation weighing a position one more or one
 * less than the model does would not agree with the rows. So the claim is held to it. For each way a
 * threshold is written, rows that the report calls enough are run against the model with a position
 * dropped, and with it weighed more, and each of those has to fail a row. Which side of the
 * threshold catches which is the comparison's — a strict one holds one value further up than a
 * non-strict one — and which way a row moves under a wrong weight is the row's, so a signed
 * position can have rows on both sides of every border and still let a weight through.
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

        /** The grade of a total: the last row of the table, whose second row is at {@code top}, it
         *  reaches. */
        int gradeOf(int m, int top) {
            int grade = 1;
            if (reaches.applyAsInt(m, 100) == 1) {
                grade = 2;
            }
            if (reaches.applyAsInt(m, top) == 1) {
                grade = 3;
            }
            return grade;
        }
    }

    private static final String SAID = "no row fixes how";

    private static final IntBinaryOperator SUM = (a, b) -> a + b;

    private static String source(Written written, String total, boolean signed, int top,
                                 List<int[]> rows) {
        return source(written, total, SUM, signed, top, rows);
    }

    /** The model's rows answer as {@code modelled} totals them, whatever {@code total} the source
     *  computes, so that a computation other than the model's is the one that is held to them. */
    private static String source(Written written, String total, IntBinaryOperator modelled,
                                 boolean signed, int top, List<int[]> rows) {
        StringBuilder out = new StringBuilder("""
                module demo

                data N = { v: Int }%s
                data Row = { grade: Int, lowerBound: Int }
                let table: List<Row> = [ Row { grade = 2, lowerBound = 100 },
                                         Row { grade = 3, lowerBound = %d } ]
                let gradeOf (m: Int): Int =
                    List.fold((acc, r) -> if %s then r.grade else acc, 1, table)

                behavior f : (a: N, b: N) -> Int

                let f (a, b) =
                    gradeOf(%s)

                example f
                """.formatted(signed ? "" : "\n    invariant v >= 0", top, written.condition,
                total));
        for (int[] row : rows) {
            out.append("    | (N { v = %d }, N { v = %d }) -> %d%n".formatted(row[0], row[1],
                    written.gradeOf(modelled.applyAsInt(row[0], row[1]), top)));
        }
        return out.toString();
    }

    /** Rows at the threshold and on each side of it, one position at a time, and one away from
     *  every border. Which of the three is where the comparison holds is the spelling's. */
    private static final List<int[]> ROWS = List.of(new int[] {1, 1},
            new int[] {99, 0}, new int[] {100, 0}, new int[] {101, 0},
            new int[] {0, 99}, new int[] {0, 100}, new int[] {0, 101});

    /**
     * Rows on both sides of both borders, with a position negative on the side where the rule does
     * not hold: weighing {@code a} twice moves every one of them to the side the model has it on,
     * so none of them catches it.
     */
    private static final List<int[]> SIGNED_ROWS = List.of(
            new int[] {100, 0}, new int[] {99, 1}, new int[] {-1, 100}, new int[] {-2, 101},
            new int[] {1000, 0}, new int[] {999, 1}, new int[] {-1, 1000}, new int[] {-2, 1001});

    private static Compilation compile(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String reportOf(Compilation model) {
        return AdequacyReport.of(model).human(SourceRendering.namedByIdentity(model.texts()));
    }

    @Test
    void rowsBesideTheThresholdFixBothWeightsHoweverTheThresholdIsWritten() {
        for (Written written : Written.values()) {
            Compilation model = compile(source(written, "a.v + b.v", false, 200, ROWS));
            assertEquals(List.of(), model.errors(), () -> written + ": the rows hold of the model");
            String report = reportOf(model);
            assertFalse(report.contains(SAID), () -> written + ": " + report);
        }
    }

    /** What the claim is for: weighing a position otherwise fails a row the report called enough. */
    @Test
    void aPositionWeighedOtherwiseFailsARowTheReportCalledEnough() {
        for (Written written : Written.values()) {
            for (String wrong : List.of("b.v", "a.v", "2 * a.v + b.v", "a.v + 2 * b.v")) {
                Compilation mutant = compile(source(written, wrong, false, 200, ROWS));
                assertFalse(mutant.errors().isEmpty(), () -> written + ": `" + wrong
                        + "` passes every row the report called enough");
            }
        }
    }

    /** The claim held to a model whose rows are on both sides and do not catch a weight: it is not
     *  called fixed, and the wrong weight is the one that passes. */
    @Test
    void rowsOnBothSidesThatAWrongWeightPassesDoNotFixThatWeight() {
        Written written = Written.AT_OR_ABOVE;
        Compilation mutant = compile(source(written, "2 * a.v + b.v", true, 1000, SIGNED_ROWS));
        assertEquals(List.of(), mutant.errors(),
                "the rows the model is held to are passed by the wrong weight");
        String report = reportOf(compile(source(written, "a.v + b.v", true, 1000, SIGNED_ROWS)));
        assertTrue(report.contains(SAID + " `a.v` weighs"), report);
        assertFalse(report.contains(SAID + " `b.v` weighs"), report);
    }

    /** Rows beside both borders of a form weighing one position by two and the other by minus one. */
    private static final List<int[]> DIFFERENCE_ROWS = List.of(
            new int[] {50, 0}, new int[] {55, 10}, new int[] {50, 1}, new int[] {55, 11},
            new int[] {51, 1}, new int[] {56, 11},
            new int[] {100, 0}, new int[] {105, 10}, new int[] {100, 1}, new int[] {105, 11},
            new int[] {101, 1}, new int[] {106, 11});

    /** The claim for a form whose weights are not one: a step is one of the quantity's own weights,
     *  and each of the four computations one step away fails a row. */
    @Test
    void aFormOfWeightsOtherThanOneIsHeldToTheSameClaim() {
        IntBinaryOperator difference = (a, b) -> 2 * a - b;
        for (Written written : Written.values()) {
            Compilation model = compile(source(written, "2 * a.v - b.v", difference, true, 200,
                    DIFFERENCE_ROWS));
            assertEquals(List.of(), model.errors(), () -> written + ": the rows hold of the model");
            assertFalse(reportOf(model).contains(SAID), () -> written + ": " + reportOf(model));
            for (String wrong : List.of("3 * a.v - b.v", "a.v - b.v", "2 * a.v", "2 * a.v - 2 * b.v")) {
                Compilation mutant = compile(source(written, wrong, difference, true, 200,
                        DIFFERENCE_ROWS));
                assertFalse(mutant.errors().isEmpty(), () -> written + ": `" + wrong
                        + "` passes every row the report called enough");
            }
        }
    }

    /** A control: rows away from the threshold fix nothing, and the report says so. */
    @Test
    void rowsNextToTheThresholdOnOneSideAreNotEnough() {
        for (Written written : Written.values()) {
            Compilation model = compile(source(written, "a.v + b.v", false, 200,
                    List.of(new int[] {1, 1}, new int[] {99, 0}, new int[] {0, 99})));
            String report = reportOf(model);
            assertTrue(report.contains(SAID + " `a.v` weighs"), () -> written + ": " + report);
        }
    }
}
