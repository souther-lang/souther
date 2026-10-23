package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.test.Nightly;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way read again for a relation eliminates numbers with no more pairs of bounds than
 * {@link CompositionBudget#PAIRS_OF_BOUNDS_A_WAY_IS_READ_AGAIN_WITH}, and where that leaves the
 * relation shown nothing, the relation says the figure is one of the reasons why.
 *
 * <p>Choices whose way apart only the bounds on {@code z + w} and {@code z - w} together show met
 * come first, each with more bounds on sums of the two beside, and choices whose way apart no
 * whole number meets come after them. Each choice kept as it stands sends the reading back to the
 * first, so the met ones are asked again each time, and each asking eliminates their numbers
 * again. The pairs run out before the walks do.
 *
 * <p>Deferred to the night because the claim is only reached past the figure, and each asking
 * reads a way of every condition of the choices met so far. That a way apart is met only where
 * the bounds together leave its numbers, and that the elimination says it stopped short, is asked
 * on every change ({@code AWitnessApartIsGivenValuesWhereTheBoundsTogetherLeaveThemTest}). What
 * only this finds is the pairs being counted over the whole reading again and the figure reaching
 * the relation, which is as well found by the morning.
 */
@Nightly
class AWayReadAgainPastItsPairsOfBoundsSaysSoTest {

    private static final int CHOICES = 8;

    @Test
    void aReadingAgainThatRunsOutOfPairsSaysSo() {
        StringBuilder inputs = new StringBuilder("x: Int, y: Int");
        StringBuilder guard = new StringBuilder("true");
        for (int each = 1; each <= CHOICES; each++) {
            String z = "z" + each;
            String w = "w" + each;
            inputs.append(", ").append(z).append(": Int, ").append(w).append(": Int");
            guard.append(" && (").append(z).append(" + ").append(w).append(" >= 2 && ")
                    .append(z).append(" + ").append(w).append(" <= 2 && ")
                    .append(z).append(" - ").append(w).append(" >= 0 && ")
                    .append(z).append(" - ").append(w).append(" <= 0");
            for (int k = 2; k <= 4; k++) {
                guard.append(" && ").append(z).append(" + ").append(k).append(" * ").append(w)
                        .append(" >= -1000 && ").append(z).append(" + ").append(k).append(" * ")
                        .append(w).append(" <= 1000");
            }
            guard.append(" || x >= ").append(each).append(")");
        }
        for (int each = 1; each <= CHOICES; each++) {
            String v = "v" + each;
            inputs.append(", ").append(v).append(": Int");
            guard.append(" && (").append(v).append(" >= 0 && ").append(v).append(" <= 1 && ")
                    .append(v).append(" /= 0 && ").append(v).append(" /= 1 || x >= ")
                    .append(each).append(")");
        }
        String source = """
                module w1
                behavior m : (%s) -> Bool
                let m (%s) = if %s then x == y else false
                """.formatted(inputs, inputs.toString().replaceAll(": [A-Za-z<>]+", ""), guard);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors());
        List<String> aboutX = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip)
                .filter(line -> line.startsWith("· not read") && line.endsWith("about `x`"))
                .toList();
        assertFalse(aboutX.isEmpty());
        assertTrue(aboutX.stream().allMatch(line ->
                line.contains(CompositionBudget.PAIRS_OF_BOUNDS_A_WAY_IS_READ_AGAIN_WITH.counts())),
                aboutX::toString);
    }
}
