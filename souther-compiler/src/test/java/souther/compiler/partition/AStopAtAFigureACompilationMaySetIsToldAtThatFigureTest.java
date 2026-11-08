package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A budget a compilation may hold to another figure ({@link Allowances#SETTABLE}) is told at the
 * figure the compilation stopped at, along every way its stop is carried to a reader: in a report
 * put together after the compilation answered, where no compilation's figures are in force.
 *
 * <p>Held for each such budget by a model whose compilation stops at it. A budget made settable is
 * held here with one, or {@link #everyBudgetACompilationMaySetIsHeldByAModelStoppingAtIt} fails:
 * which ways its stop is carried along is what the model's report reads, and a way that makes the
 * figure again where it is told says the one declared.
 */
class AStopAtAFigureACompilationMaySetIsToldAtThatFigureTest {

    /** A model whose compilation stops at a budget, held to {@code figure}, not the one declared. */
    private record Stopping(String model, int figure) {}

    /**
     * The first of seven thresholds two numbers and their sum are all above, compared: each line
     * decides where every threshold before the one found was missed, more ways of choosing than
     * none, so with none taken apart every line is cut off.
     */
    private static final Map<CompositionBudget, Stopping> STOPPING = Map.of(
            CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO, new Stopping("""
                    module demo exposing (g)

                    behavior g : (x: Int, y: Int) -> Bool
                    let g (x, y) =
                        Option.withDefault(0, List.find(t -> x > t && y > t && x + y > t,
                            [1, 2, 3, 4, 5, 6, 7])) > 3
                    """, 0));

    @Test
    void everyBudgetACompilationMaySetIsHeldByAModelStoppingAtIt() {
        assertEquals(Allowances.SETTABLE, STOPPING.keySet());
    }

    @Test
    void aStopIsToldAtTheFigureItsCompilationWasHeldTo() {
        STOPPING.forEach((budget, stopping) -> {
            assertTrue(stopping.figure() != budget.declared(), "a figure other than declared");
            Compilation compilation = Compilation.ofSource(stopping.model(), "Main")
                    .allowing(Allowances.DECLARED.with(budget, stopping.figure()));
            compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors());
            assertEquals(budget.declared(), budget.maximum(), "told where none is in force");

            String said = AdequacyReport.of(compilation)
                    .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
            List<String> stops = said.lines()
                    .filter(each -> each.contains(budget.name() + ",")).toList();
            assertFalse(stops.isEmpty(), () -> budget + " is said where it stopped: " + said);
            for (String each : stops) {
                assertTrue(each.contains("(" + budget.name() + ", " + stopping.figure() + ")"),
                        () -> "at the figure it was held to: " + each);
            }
        });
    }
}
