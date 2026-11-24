package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.Generator;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.publish.PublicationOrders;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a second stage of a search was short of is an outcome beside the first stage's, and is read
 * as every outcome is: as a gap of its own, whatever the first stage came to.
 *
 * <p>What was built and where the search was incomplete are two facts. Written onto the outcomes
 * of the first stage, an outcome that is a row had nowhere to carry the second, and a stage that
 * came to a stop, a limit or a population each took it in its own way — or took nothing.
 */
class WhatASecondStageWasShortOfIsAnOutcomeBesideTheFirstsTest {

    private static final CompositionBudget EARLIER = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS;

    private static final CompositionBudget LATER =
            CompositionBudget.ROWS_BESIDE_A_RUN_ARE_MADE_FOR_A_POINT;

    private static final CompositionRepertoire WALKED =
            CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_SIZES;

    private static final Generator.UnresolvedCombination NOT_FOUND =
            new Generator.UnresolvedCombination(List.of("p"),
                    Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS);

    private static ItemAssessment.Attempt secondStage(CompositionShortfall short_) {
        return ItemAssessment.Attempt.ofAStageShortOf(NOT_FOUND, WayToTheBorder.UNTOUCHED,
                short_);
    }

    private static ItemAssessment.Attempt.Unexhausted walkedSomeOf() {
        return new ItemAssessment.Attempt.Unexhausted(NOT_FOUND, WayToTheBorder.UNTOUCHED,
                CompositionAccount.NOTHING,
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of(WALKED)),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(Set.of()));
    }

    private static ItemAssessment.Attempt.Limited limitedBy(CompositionBudget figure) {
        return new ItemAssessment.Attempt.Limited(NOT_FOUND, WayToTheBorder.UNTOUCHED,
                CompositionAccount.NOTHING,
                PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of(figure)),
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of()),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(Set.of()));
    }

    /** A figure is why: the outcome is the one a figure limited, and says which. */
    @Test
    void aStageAFigureStoppedIsAnOutcomeLimitedByIt() {
        ItemAssessment.Attempt.Limited stage = (ItemAssessment.Attempt.Limited)
                secondStage(CompositionShortfall.of(Set.of(LATER)));

        assertEquals(List.of(LATER), stage.limitedBy().written());
    }

    /** No figure: the stage walked some of a population, and the outcome says which. */
    @Test
    void aStageThatWalkedSomeOfAPopulationIsAnOutcomeThatSaysWhich() {
        ItemAssessment.Attempt.Unexhausted stage = (ItemAssessment.Attempt.Unexhausted)
                secondStage(CompositionShortfall.writing(Set.of(WALKED)));

        assertEquals(List.of(WALKED), stage.notAllOf().written());
    }

    /** A stage short of nothing came to nothing for the model's reason, and has no outcome. */
    @Test
    void aStageShortOfNothingIsNotAnOutcomeOfThisKind() {
        assertThrows(IllegalArgumentException.class, () -> secondStage(CompositionShortfall.NONE));
    }

    /**
     * Both are reported, whatever the first stage came to: the gap of the first stage and the gap
     * of the second are two entries, and the second does not replace the first or wait on its shape.
     */
    @Test
    void theGapOfEachStageIsReportedWhateverTheFirstCameTo() {
        for (ItemAssessment.Attempt first : List.of(walkedSomeOf(), limitedBy(EARLIER))) {
            SearchOutcomes outcomes = SearchOutcomes.of(first)
                    .plus(SearchOutcomes.of(secondStage(CompositionShortfall.of(Set.of(LATER)))));

            assertEquals(2, outcomes.prevented().size(), first.toString());
            assertTrue(outcomes.prevented().keySet().stream().anyMatch(gap ->
                    gap.equals(((ItemAssessment.Attempt.Prevented) first).by())), first.toString());
        }
    }

    /** A stage that was cut is no proof that nothing is there, and no outcome beside it makes one. */
    @Test
    void aSearchWhoseSecondStageWasCutProvesNothing() {
        ItemAssessment.Attempt.Unresolved none = new ItemAssessment.Attempt.Unresolved(
                new Generator.UnresolvedCombination(List.of("p"),
                        Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE),
                WayToTheBorder.UNTOUCHED);

        assertTrue(SearchOutcomes.of(none).provesInfeasible());
        assertFalse(SearchOutcomes.of(none)
                .plus(SearchOutcomes.of(secondStage(CompositionShortfall.of(Set.of(LATER)))))
                .provesInfeasible());
    }
}
