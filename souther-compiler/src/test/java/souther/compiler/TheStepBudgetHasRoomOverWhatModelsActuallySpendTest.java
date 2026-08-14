package souther.compiler;

import souther.compiler.examples.EvaluationPolicy;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The default budget is set over what models actually spend, and this keeps it there.
 *
 * <p>A default chosen once and never checked again drifts: the emitter gains a counted point, a
 * library helper is rewritten as a fold, and one day a model that has not changed stops compiling.
 * What stops that is not a bigger number but a measurement — what the heaviest row anyone has written
 * costs, held against what the budget allows, with room between them said out loud.
 *
 * <p>The margin is what makes this a check rather than a tautology. A corpus that reached even a
 * tenth of the budget would be one where the next model written is the one that fails, and the answer
 * then is to look at why a row costs that much before reaching for a larger default.
 */
class TheStepBudgetHasRoomOverWhatModelsActuallySpendTest {

    /**
     * How much of the budget the heaviest row may cost before this fails.
     *
     * <p>A hundredfold. Two orders of magnitude is room for a model an order of magnitude heavier
     * than anything written so far, and for the emitter to grow a counted point in a loop that
     * already had one, without either being a change that stops a build somewhere.
     */
    private static final long SAFETY_FACTOR = 100L;

    /** A row that walks a list and builds a value per element: what an example that does real work
     *  looks like, and the shape most likely to be the heaviest one in a corpus. */
    private static String walking(int elements) {
        StringBuilder items = new StringBuilder();
        for (int i = 0; i < elements; i++) {
            items.append(i == 0 ? "" : ", ").append("Item { code = \"c-").append(i)
                    .append("\", qty = ").append(i % 7).append(" }");
        }
        return """
                module example.census

                data Item = { code: String, qty: Int }
                data Basket = { items: List<Item> }
                data Total = Int
                data Counted = { total: Total }

                behavior tally : (basket: Basket) -> Counted
                    constructs Counted, Total

                let tally (basket) = Counted {
                    total = Total(List.fold((sum, item) -> sum + item.qty, 0, basket.items))
                }

                example tally
                    | "a basket" : (Basket { items = [ %s ] }) -> Counted { total = Total(%d) }
                """.formatted(items, expectedTotal(elements));
    }

    private static int expectedTotal(int elements) {
        int total = 0;
        for (int i = 0; i < elements; i++) {
            total += i % 7;
        }
        return total;
    }

    /** What every row of {@code source} cost, in the unit it is held to. */
    private static List<RowOutcome> rowsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        souther.compiler.diag.CompileException wrong =
                compilation.failure(compilation.db().allReports());
        if (wrong != null) {
            throw new IllegalStateException("the census model has to compile: " + wrong.getMessage());
        }
        List<RowOutcome> rows = new ArrayList<>();
        for (String sourceId : compilation.exampleSourcesOf("example.census")) {
            Output.Examples.Of observed = compilation.db()
                    .ask(new Output.Examples("example.census", sourceId, Output.CoverageMode.NONE))
                    .value();
            rows.addAll(observed.rows());
        }
        return rows;
    }

    /**
     * The heaviest row anyone is likely to write stays well inside the default.
     *
     * <p>Two thousand elements is larger than any row in this compiler's own models and larger than
     * the fixtures its examples carry, so what it costs is an upper bound on them rather than a
     * sample of them.
     */
    @Test
    void theHeaviestRowCostsFarLessThanTheDefaultAllows() {
        List<RowOutcome> rows = rowsOf(walking(2_000));

        assertTrue(rows.stream().allMatch(row -> row.disposition() == Disposition.HELD),
                "the census model has to be one that holds: " + rows);
        long heaviest = rows.stream().mapToLong(TheStepBudgetHasRoomOverWhatModelsActuallySpendTest::steps).max().orElse(0L);
        assertTrue(heaviest > 0, "a row that walks two thousand elements costs counted points");
        assertTrue(heaviest * SAFETY_FACTOR < EvaluationPolicy.DEFAULT_STEP_LIMIT,
                "the heaviest row spent " + heaviest + " steps against a default of "
                        + EvaluationPolicy.DEFAULT_STEP_LIMIT + ", which leaves less than "
                        + SAFETY_FACTOR + "x of room");
    }

    /** And what a row costs is proportional to what it does, so the number means something: a row
     *  over twice the elements costs about twice as much. */
    @Test
    void whatARowCostsFollowsWhatItWalks() {
        long small = steps(rowsOf(walking(500)).get(0));
        long large = steps(rowsOf(walking(1_000)).get(0));

        assertTrue(large > small, "walking twice as much costs more: " + small + " then " + large);
        assertTrue(large < small * 4,
                "and not disproportionately more: " + small + " then " + large);
    }

    /** What a row spent: the counted work of its whole evaluation, fixtures and application alike. */
    private static long steps(RowOutcome row) {
        return row.run().counted().steps();
    }

}
