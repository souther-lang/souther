package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.observe.Figure;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two accounts of one place, from two relations of a comparison or two ways to it, are one account
 * that keeps every figure either search stopped at: putting them together loses neither side's.
 */
class WhatSeveralSearchesShowOfOnePlaceKeepsEveryFigureTheyStoppedAtTest {

    private static final Figure ONE = CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure();

    private static final Figure OTHER = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.figure();

    @Test
    void placesShownByTwoSearchesSayBothFigures() {
        UndividedByARelation.GettingThere first = new UndividedByARelation.GettingThere(
                List.of(), Set.of(), Set.of(ONE));
        UndividedByARelation.GettingThere second = new UndividedByARelation.GettingThere(
                List.of("\"a\""), Set.of(), Set.of(OTHER));

        UndividedByARelation.GettingThere both = first.and(second);

        assertEquals(Set.of(ONE, OTHER), both.stoppedAt());
        assertEquals(List.of("\"a\""), both.reachedAt());
        assertEquals(Figure.inOrder(List.of(ONE, OTHER)), both.reason().stoppedAt());
    }

    @Test
    void twoAccountsOfTheWordPutTogetherSayBothFigures() {
        BlockReason.RelationNotShownReachedAtEveryValue first =
                new BlockReason.RelationNotShownReachedAtEveryValue(List.of(), List.of(),
                        List.of(ONE));
        BlockReason.RelationNotShownReachedAtEveryValue second =
                new BlockReason.RelationNotShownReachedAtEveryValue(List.of("\"a\""), List.of(),
                        List.of(OTHER));

        BlockReason.RelationNotShownReachedAtEveryValue both = BlockReason.together(first, second);

        assertEquals(Figure.inOrder(List.of(ONE, OTHER)), both.stoppedAt());
        assertEquals(BlockReason.factOf(first), BlockReason.factOf(second),
                "figures are evidence of the reason and do not tell two reasons apart");
    }
}
