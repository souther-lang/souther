package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point that lies only where a disequality has taken a value out of a whole-numbered position
 * is one no row can stand at, as a point outside an interval guard is.
 *
 * <p>The hole is inside the run the position is projected onto, so only the region's own
 * algebra finds it, and it is handed the point's bounds as numbers of the position.
 */
class APointInTheHoleOfADisequalityIsProvedEmptyTest {

    private static final String THRESHOLD_AFTER_THE_EQUALITY = """
            module m

            behavior f : (n: Int) -> Int

            let f (n) = if n == 50 then 3 else (if n >= 50 then 1 else 2)

            example f
                | (50) -> 3
                | (49) -> 2
                | (51) -> 1
                | (0) -> 2
                | (60) -> 1
            """;

    /** The comparison's ON point is 51, which the hole leaves. */
    private static final String THRESHOLD_BESIDE_THE_HOLE = """
            module m

            behavior f : (n: Int) -> Int

            let f (n) = if n == 50 then 3 else (if n >= 51 then 1 else 2)

            example f
                | (50) -> 3
                | (49) -> 2
                | (51) -> 1
                | (0) -> 2
                | (60) -> 1
            """;

    private static final String BELOW_THE_EQUALITY = """
            module m

            behavior f : (n: Int) -> Int

            let f (n) = if n == 50 then 3 else (if n <= 50 then 1 else 2)

            example f
                | (50) -> 3
                | (49) -> 1
                | (51) -> 2
                | (0) -> 1
                | (60) -> 2
            """;

    @Test
    void theOnPointInTheHoleIsOneNoRowCanStandAt() {
        String page = report(THRESHOLD_AFTER_THE_EQUALITY);

        assertTrue(page.contains("no row can stand at the ON point"),
                () -> "the point in the hole is refuted: " + page);
        assertFalse(page.contains("nothing composed one"),
                () -> "no search is blamed for a point that has no row: " + page);
    }

    @Test
    void theOnPointBelowTheHoleIsOneNoRowCanStandAt() {
        String page = report(BELOW_THE_EQUALITY);

        assertTrue(page.contains("no row can stand at the ON point"),
                () -> "the point in the hole is refuted from below too: " + page);
    }

    @Test
    void aPointNextToTheHoleIsNotRefuted() {
        String page = report(THRESHOLD_BESIDE_THE_HOLE);

        assertFalse(page.contains("no row can stand at the ON point"),
                () -> "a point the hole leaves is still owed a row: " + page);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
