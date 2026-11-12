package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A call that ends a run on a divisor which is a list total owes a row the divisor is off nought
 * at, and the row that has it is one whose list holds an element: what stands for a list holds
 * nothing, and its total is nought. The list is a field of the row the behavior takes, at any
 * depth, so the elements are tried where the list is and not only where the parameter is.
 */
class ADivisorThatIsAListTotalIsAnsweredByARowHoldingAnElementTest {

    private static final String DECLARED = """
            module probe.total

            data Ok
            data No
            data Skipped

            data Row = { xs: List<Int>, m: Int, j: Int }
            data Outer = { inner: Row }
            data Pair = { xs: List<Int>, ys: List<Int>, m: Int, j: Int }
            data Flat = { xs: List<Int>, m: Int, j: Int } invariant List.sum(xs) == 0
            """;

    private record Model(String name, String parameter, String before, String comparison) {}

    private static final List<Model> READ = List.of(
            new Model("a remainder by a total", "Row",
                    "let y = Int.floorMod(7, List.sum(p.xs))", "p.m + 1 >= p.j"),
            new Model("a quotient by a total", "Row",
                    "let y = Rational.toInt(DOWN, 1 / List.sum(p.xs))", "p.m + 1 >= p.j"),
            new Model("a quotient by a total, undone", "Row",
                    "let y = 1 / List.sum(p.xs)", "p.m + 1 >= p.j"),
            new Model("a remainder by a total of a list in a record in the row", "Outer",
                    "let y = Int.floorMod(7, List.sum(p.inner.xs))",
                    "p.inner.m + 1 >= p.inner.j"),
            // Each total is to be off nought together, which a row making one of them so does not
            // do: both lists are in the one record.
            new Model("a remainder by each of two totals", "Pair",
                    "let a = Int.floorMod(7, List.sum(p.xs))\n"
                            + "    let b = Int.floorMod(7, List.sum(p.ys))",
                    "p.m + 1 >= p.j"));

    private static String source(Model model) {
        return DECLARED + """

                behavior m : (p: %s) -> Bool
                let m (p) = {
                    %s
                    let c = %s
                    c
                }
                """.formatted(model.parameter(), model.before(), model.comparison());
    }

    private static String report(Model model, Adequacy.Level level) {
        Compilation compilation = Compilation.ofSource(source(model), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(level));
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void aComparisonBesideATotalTheRowSearchCanOffAnythingIsReadAtEveryLevel() {
        List<String> wrong = new ArrayList<>();
        for (Model each : READ) {
            String report = report(each, Adequacy.Level.ALL);
            if (report.contains("not read:")) {
                wrong.add(each.name() + " is not read:\n" + report);
            }
        }
        assertEquals(List.of(), wrong);
    }

    /**
     * A row that gets to the comparison shows some run gets past what a run to it works out
     * whenever it works out the part it is read in. Where some runs take the other arm, or do not
     * run the right operand, a row that gets to the comparison by one of them has not worked the
     * operator out, and what the row shows of it is nothing.
     *
     * <p>The total of the list is nought in every row, so the remainder stops every run that works
     * it out: the comparison is reached only where the run does not, which is where the arm or
     * the operand that holds it is skipped — and that is decided by {@code p.m}, which the
     * comparison reads. A value of {@code p.m} on the other side of the decision is a value no run
     * gets to the comparison at.
     */
    @Test
    void aStopOnlySomeRunsWorkOutIsNotAnsweredByARowThatDidNotWorkItOut() {
        List<Model> skipped = List.of(
                new Model("a remainder in the arm of a choice", "Flat",
                        "let y = if p.m > 0 then Int.floorMod(7, List.sum(p.xs)) else 0",
                        "p.m + 1 >= p.j"),
                new Model("a remainder in the other arm of a choice", "Flat",
                        "let y = if p.m > 0 then 0 else Int.floorMod(7, List.sum(p.xs))",
                        "p.m + 1 >= p.j"),
                new Model("a remainder on the right of a conjunction", "Flat",
                        "let y = p.m > 0 && Int.floorMod(7, List.sum(p.xs)) > 0",
                        "p.m + 1 >= p.j"),
                new Model("a remainder on the right of a disjunction", "Flat",
                        "let y = p.m > 0 || Int.floorMod(7, List.sum(p.xs)) > 0",
                        "p.m + 1 >= p.j"));
        List<String> wrong = new ArrayList<>();
        for (Model each : skipped) {
            String report = report(each, Adequacy.Level.ALL);
            if (!report.contains("not read:")) {
                wrong.add(each.name() + " is read:\n" + report);
            }
        }
        assertEquals(List.of(), wrong);
    }

    /**
     * What a condition over two totals asks is not what a list holding one element answers, so no
     * row is made up for it: what is not found is not said to be read.
     */
    @Test
    void aDivisorOverTwoTotalsIsNotAnsweredByARowMadeUpForOne() {
        Model pinned = new Model("a remainder by two totals", "Pair",
                "let y = Int.floorMod(7, List.sum(p.xs) + List.sum(p.ys))", "p.m + 1 >= p.j");
        String report = report(pinned, Adequacy.Level.ALL);
        assertTrue(report.contains("not read:"), report);
        assertFalse(report.contains("a row was run to it"), report);
    }
}
