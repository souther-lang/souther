package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionCapacity;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.Generator;
import souther.compiler.partition.Realization;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.publish.PublicationOrders;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk that met a figure and also reached a number it could not hold says both, from the answer
 * the search comes back with to the gap a report reads.
 *
 * <p>The two readings of a pair walk one order, so one of them may stop at a figure while the other
 * stops at a place it cannot hold. What a reader does about each differs — raise the figure, or run
 * with more room, or nothing — and a step that kept one of them and dropped the other would tell a
 * reader to act on half of what left the point open.
 */
class AFigureAndANumberNotHeldTravelTogetherTest {

    private static final Set<CompositionBudget> FIGURE =
            Set.of(CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT);

    private static final Set<CompositionCapacity> NOT_HELD = Set.of(new CompositionCapacity(
            CompositionCapacity.Where.PLACES_A_PAIR_IS_WALKED_TO,
            UnheldNumber.NO_REPRESENTATION_EXISTS));

    private static final Set<CompositionRepertoire> WRITES_SOME_OF =
            Set.of(CompositionRepertoire.PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE);

    /**
     * The word a walk comes back with is decided once, and every set goes with it.
     *
     * <p>The figure decides the word where there is one, since that is checked against the figure
     * at both ends; a walk with no figure that left anything untried says so; and a walk that left
     * nothing comes back with its own word.
     */
    @Test
    void theWordIsDecidedOnceAndEverySetGoesWithIt() {
        Realization.Unknown all = Realization.Unknown.leftOpen(
                Realization.Unknown.Reason.NOTHING_COMPOSED_ONE, FIGURE, WRITES_SOME_OF, NOT_HELD);
        assertEquals(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE, all.why(),
                "the pair's figure comes back with the word it always has");
        assertEquals(FIGURE, all.stoppedBy());
        assertEquals(WRITES_SOME_OF, all.notAllOf());
        assertEquals(NOT_HELD, all.unheld());

        assertEquals(Realization.Unknown.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED,
                Realization.Unknown.leftOpen(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE,
                        Set.of(), Set.of(), NOT_HELD).why(),
                "a number not held is something left untried");
        assertEquals(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE,
                Realization.Unknown.leftOpen(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE,
                        Set.of(), Set.of(), Set.of()).why(),
                "and a walk that left nothing says its own word, which is the control");
    }

    /**
     * And the figure with the number not held reaches the gap a report reads, through each arm a
     * search's answer can be carried in.
     */
    @Test
    void theGapHoldsTheFigureAndTheNumberNotHeld() {
        Generator.UnresolvedCombination word = new Generator.UnresolvedCombination(
                List.of("p.a - p.b = 0"), Generator.UnresolvedCombination.Reason.wordFor(FIGURE));
        ItemAssessment.Attempt.Stopped stopped = new ItemAssessment.Attempt.Stopped(word,
                WayToTheBorder.UNTOUCHED, CompositionAccount.NOTHING,
                PublicationOrders.COMPOSITION_BUDGETS.keep(FIGURE),
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of()),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(NOT_HELD));
        ItemAssessment.Attempt.Limited limited = new ItemAssessment.Attempt.Limited(word,
                WayToTheBorder.UNTOUCHED, CompositionAccount.NOTHING,
                PublicationOrders.COMPOSITION_BUDGETS.keep(FIGURE),
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of()),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(NOT_HELD));

        for (ItemAssessment.Attempt.Prevented each : List.of(stopped, limited)) {
            EstablishmentGap.Composition gap = (EstablishmentGap.Composition)
                    WritabilityKnowledge.Prevented.of(List.of(each.by())).by().written()
                            .getFirst();
            assertEquals(List.copyOf(FIGURE), gap.budgets().written(), each::toString);
            assertEquals(List.copyOf(NOT_HELD), gap.capacities().written(), each::toString);
        }
    }
}
