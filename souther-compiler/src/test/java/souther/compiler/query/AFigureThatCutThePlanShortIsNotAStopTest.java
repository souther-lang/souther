package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.Generator;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.publish.PublicationOrders;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A line's search over a plan a figure cut short, or one nothing was planned for, is carried as
 * that and not as a search the figure stopped.
 *
 * <p>The reading of a line hands its searches on in the value a report says them from
 * ({@link CameToNothing}), and a figure there in the place of one that stopped a search is said as
 * a stop. The search ran to the end of what it was handed, or was never made.
 */
class AFigureThatCutThePlanShortIsNotAStopTest {

    private static final Set<CompositionBudget> PLAN =
            Set.of(CompositionBudget.DEPTH_A_CONSTRUCTION_PLAN_DESCENDS);

    @Test
    void aSearchOverACutPlanIsHeldAsOne() {
        CameToNothing came = ARowTellingTheLinesApart.cameToNothing(
                new ItemAssessment.Attempt.Limited(word(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE),
                        WayToTheBorder.UNTOUCHED, CompositionAccount.NOTHING,
                        PublicationOrders.COMPOSITION_BUDGETS.keep(PLAN),
                        PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of()),
                        PublicationOrders.COMPOSITION_CAPACITIES.keep(Set.of())));

        assertEquals(CompositionShortfall.NONE, came.met(), "nothing stopped the search");
        assertEquals(PLAN, came.planCut(), "the figure cut short the plan it ran over");
    }

    @Test
    void aSearchNothingWasPlannedForIsHeldAsOne() {
        CameToNothing came = ARowTellingTheLinesApart.cameToNothing(
                new ItemAssessment.Attempt.Unplanned(word(
                        Generator.UnresolvedCombination.Reason
                                .NO_READING_OF_THE_LINE_COULD_BE_SEARCHED),
                        WayToTheBorder.UNTOUCHED, CompositionAccount.NOTHING,
                        PublicationOrders.COMPOSITION_BUDGETS.keep(PLAN)));

        assertEquals(CompositionShortfall.NONE, came.met(), "no search was made to stop");
        assertEquals(PLAN, came.planCut(), "the figure left nothing planned");
    }

    private static Generator.UnresolvedCombination word(
            Generator.UnresolvedCombination.Reason reason) {
        return new Generator.UnresolvedCombination(List.of("a line"), reason);
    }
}
