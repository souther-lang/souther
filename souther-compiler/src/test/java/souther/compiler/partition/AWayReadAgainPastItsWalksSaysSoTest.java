package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.test.Nightly;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way read again for a relation is read with no more walks than
 * {@link CompositionBudget#WALKS_A_WAY_IS_READ_AGAIN_WITH}, and where that leaves the relation
 * shown nothing, the relation says the figure is one of the reasons why.
 *
 * <p>Twenty choices whose way apart is met come first, and twenty whose way apart no whole number
 * meets come after them, though the walk finds nothing closed on that way. Each choice kept as it
 * stands sends the reading back to the first, so the met ones are asked again each time, and the
 * walks run out before the last of the others is reached.
 *
 * <p>Deferred to the night because the claim is only reached past the figure: no model reaches
 * it with fewer walks than it allows, and each walk reads a way of forty conditions. Which figure
 * a relation names is read off the same carrier for the ways looked along, which
 * {@code ARelationLeavesAPlaceUndividedOnlyWhereTheOtherSideIsShownToReachItTest} asks on every
 * change. What only this finds is the count of walks being kept, which is as well found by the
 * morning.
 */
@Nightly
class AWayReadAgainPastItsWalksSaysSoTest {

    @Test
    void aReadingAgainThatRunsOutOfWalksSaysSo() {
        StringBuilder inputs = new StringBuilder("x: Int, y: Int");
        StringBuilder guard = new StringBuilder("true");
        for (int each = 1; each <= 20; each++) {
            inputs.append(", w").append(each).append(": Int");
            guard.append(" && (w").append(each).append(" /= 0 || x >= ").append(each)
                    .append(")");
        }
        for (int each = 1; each <= 20; each++) {
            String z = "z" + each;
            inputs.append(", ").append(z).append(": Int");
            guard.append(" && (").append(z).append(" >= 0 && ").append(z).append(" <= 1 && ")
                    .append(z).append(" /= 0 && ").append(z).append(" /= 1 || x >= ")
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
        List<String> aboutX = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip)
                .filter(line -> line.startsWith("· not read") && line.endsWith("about `x`"))
                .toList();
        assertFalse(aboutX.isEmpty());
        assertTrue(aboutX.stream().allMatch(line ->
                line.contains(CompositionBudget.WALKS_A_WAY_IS_READ_AGAIN_WITH.counts())
                        && line.contains(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.counts())),
                aboutX::toString);
    }
}
