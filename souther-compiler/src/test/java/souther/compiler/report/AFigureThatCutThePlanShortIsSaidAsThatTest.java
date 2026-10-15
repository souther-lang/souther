package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.Generator;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A figure that cut short the plan a search ran over is said as that, and never as a figure the
 * search stopped at.
 *
 * <p>The search ran to the end of what it was handed, or was never made. Told it stopped, a reader
 * goes looking for a search that did not finish; told its plan was cut short, they read the word
 * after it as being about less than there was.
 */
class AFigureThatCutThePlanShortIsSaidAsThatTest {

    @Test
    void aCutPlanIsNotSaidAsAStop() {
        String said = Reasons.met(new CameToNothing(word(), CompositionShortfall.NONE,
                Set.of(CompositionBudget.DEPTH_A_CONSTRUCTION_PLAN_DESCENDS)));

        assertFalse(said.contains("stopped at"), said);
        assertTrue(said.startsWith("this compiler's plan of the value was limited by "), said);
    }

    /** And a search that met a figure and was handed a cut plan is said as both, the stop first. */
    @Test
    void aStopAndACutPlanAreBothSaid() {
        String said = Reasons.met(new CameToNothing(word(),
                CompositionShortfall.of(Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS)),
                Set.of(CompositionBudget.DEPTH_A_CONSTRUCTION_PLAN_DESCENDS)));

        assertTrue(said.startsWith("this compiler stopped at "), said);
        assertTrue(said.contains(", and this compiler's plan of the value was limited by "), said);
    }

    private static Generator.UnresolvedCombination word() {
        return new Generator.UnresolvedCombination(List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
    }
}
