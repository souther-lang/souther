package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rows made beside the rows a point's candidates ran were short of is said in the
 * vocabulary it was short in. The figure of rows made is reached only by a candidate being asked
 * for after it was spent, and whatever else the building of a value met is not turned into it.
 */
class WhatStoppedTheRowsBesideARunIsSaidAsWhatItWasTest {

    private static final CompositionBudget FIGURE =
            CompositionBudget.ROWS_BESIDE_A_RUN_ARE_MADE_FOR_A_POINT;

    /** Using none of the figure, or all of it, is not reaching it. */
    @Test
    void aSearchThatSpentWhatItWasGivenAndAskedForNoMoreIsShortOfNothing() {
        Generator.RowsBesideBudget budget = new Generator.RowsBesideBudget();

        for (int made = 0; made < FIGURE.maximum(); made++) {
            assertTrue(budget.oneMore(), "candidate " + made);
        }

        assertTrue(budget.shortOf().nothing(), budget.shortOf().toString());
    }

    /** The first candidate asked for past the figure is the one it stopped. */
    @Test
    void aCandidateAskedForPastTheFigureSaysTheFigureWasReached() {
        Generator.RowsBesideBudget budget = new Generator.RowsBesideBudget();
        for (int made = 0; made < FIGURE.maximum(); made++) {
            budget.oneMore();
        }

        assertFalse(budget.oneMore());

        assertEquals(Set.of(FIGURE), budget.shortOf().figures());
    }

    /** The values made of a type are held to the same figure, and reaching it is reaching it. */
    @Test
    void theValuesMadeOfATypeReachingTheFigureSaysTheFigureWasReached() {
        Generator.RowsBesideBudget budget = new Generator.RowsBesideBudget();

        budget.valuesCutShort();

        assertEquals(Set.of(FIGURE), budget.shortOf().figures());
    }

    /**
     * A building of a value that met nothing says so, and is not a figure reached. It is said at
     * every value made, so a search that is told this as a stop would name the figure for every
     * point that grew a list.
     */
    @Test
    void aBuildingThatMetNothingIsNotAStop() {
        Generator.RowsBesideBudget budget = new Generator.RowsBesideBudget();

        budget.met(CompositionShortfall.NONE);

        assertTrue(budget.shortOf().nothing(), budget.shortOf().toString());
    }

    /** What the building met is kept as what it is, each in its own vocabulary. */
    @Test
    void whatABuildingMetIsKeptInItsOwnVocabularyAndNotAsTheFigure() {
        Generator.RowsBesideBudget budget = new Generator.RowsBesideBudget();
        CompositionBudget other = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS;
        CompositionRepertoire population =
                CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_SIZES;

        budget.met(CompositionShortfall.of(Set.of(other), Set.of(population), Set.of()));

        CompositionShortfall short_ = budget.shortOf();
        assertEquals(Set.of(other), short_.figures());
        assertEquals(Set.of(population), short_.populations());
        assertFalse(short_.figures().contains(FIGURE));
    }
}
