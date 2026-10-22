package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A point a run gets to only past something worked out on operands nothing here says is owed and
 * counted, and is no gap.
 *
 * <p>{@code a * n} over two whole numbers nothing bounds answers where their product fits an
 * {@code Int}, which no form here says. What arrives at {@code b > 3} past it is what has to hold
 * for a run to be there — {@code b} is any number — and that is read; that a run holding it gets
 * there is not. So a value read back at {@code b = 4} shows no run getting there with it: what does
 * is a row composed for the point and seen run to the comparison. Where one was, the point is a gap
 * like any other; where none was, it stays owed, in the count, and open on the way there.
 *
 * <p>Beside a sum, whose region is read: {@code a + n} answers where it fits, which is a form, and
 * the point past it is a gap whatever was run. The bodies differ in the one operator.
 */
class APointPastSomethingNothingReadsTheAnswerOfIsOwedAndNoGapTest {

    private static String report(String worked) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior f : (a: Int, n: Int, b: Int) -> Ok | No
                let f (a, n, b) = {
                    let c = %s
                    guard b > 3 else No
                    Ok
                }
                example f
                    | "low" : (1, 1, 0) -> No
                    | "high" : (1, 1, 9) -> Ok
                """.formatted(worked), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** What the report says of the border's points no row is at, a line each. */
    private static List<String> openAtTheBorder(String report) {
        return report.lines().map(String::strip)
                .filter(line -> line.contains("point (comparison@5:13)"))
                .filter(line -> line.startsWith("?") || line.startsWith("!"))
                .toList();
    }

    /**
     * Past a product nothing bounds, a row composed for each point is run, and the run is seen at
     * the comparison: that shows a run gets there, so the point is a gap like any other. What stays
     * open where no composed row was seen there is held in {@code ObligationDisposition}'s own test.
     */
    @Test
    void aPointPastAProductNothingBoundsIsAGapWhereARowWasRunThere() {
        String report = report("a * n");
        assertEquals(List.of(
                "! no row is at the ON point (comparison@5:13)",
                "! no row is at the OFF point (comparison@5:13)"),
                openAtTheBorder(report), report);
    }

    @Test
    void aPointPastASumIsAGap() {
        String report = report("a + n");
        assertEquals(List.of(
                "! no row is at the ON point (comparison@5:13)",
                "! no row is at the OFF point (comparison@5:13)"),
                openAtTheBorder(report), report);
    }

    /** A product of two values the guards hold to small ends answers wherever they hold, which is
     *  read, and the point past it is a gap. */
    @Test
    void aPointPastAProductTheGuardsKeepSmallIsAGap() {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior f : (a: Int, n: Int, b: Int) -> Ok | No
                let f (a, n, b) = {
                    guard a >= 0 && a <= 100 else No
                    guard n >= 0 && n <= 100 else No
                    let c = a * n
                    guard b > 3 else No
                    Ok
                }
                example f
                    | "low" : (1, 1, 0) -> No
                    | "high" : (1, 1, 9) -> Ok
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertEquals(List.of(
                "! no row is at the ON point (comparison@7:13)",
                "! no row is at the OFF point (comparison@7:13)"),
                report.lines().map(String::strip)
                        .filter(line -> line.contains("point (comparison@7:13)"))
                        .filter(line -> line.startsWith("?") || line.startsWith("!"))
                        .toList(), report);
    }
}
