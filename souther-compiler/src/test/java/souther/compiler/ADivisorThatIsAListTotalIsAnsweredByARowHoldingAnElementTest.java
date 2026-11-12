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
                    "p.inner.m + 1 >= p.inner.j"));

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
