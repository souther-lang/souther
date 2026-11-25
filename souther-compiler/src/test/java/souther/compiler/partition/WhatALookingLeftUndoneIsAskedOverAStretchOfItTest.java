package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a looking for a row left undone is asked over the stretch of it a reader put together, and
 * is what happened in that stretch: not before it, and not a figure that ran out exactly as the
 * last of its work was done.
 */
class WhatALookingLeftUndoneIsAskedOverAStretchOfItTest {

    private static final CompositionBudget SEARCHES =
            CompositionBudget.SEARCHES_A_ROW_IS_COMPOSED_THROUGH;

    @Test
    void theLastSearchSpentOnTheLastAttemptLeftNothingUndone() {
        LookingForARow looking = new LookingForARow(2);
        LookingForARow.Mark from = looking.from();
        looking.attempt();
        looking.attempt();
        assertEquals(Set.of(), from.leftAt(), "both searches spent, and nothing asked past them");
    }

    @Test
    void anAttemptAskedForWithNoSearchLeftIsWhatTheStretchLeftUndone() {
        LookingForARow looking = new LookingForARow(1);
        LookingForARow.Mark from = looking.from();
        looking.attempt();
        looking.left();
        assertEquals(Set.of(SEARCHES), from.leftAt(), "an attempt was in front and none was left");
    }

    /** A stretch that starts after the looking ran out says only what ran out inside it. */
    @Test
    void whatWasLeftBeforeAStretchIsNotItsOwn() {
        LookingForARow looking = new LookingForARow(1);
        looking.attempt();
        looking.left();
        LookingForARow.Mark after = looking.from();
        assertEquals(Set.of(), after.leftAt(), "nothing asked for since");
        looking.left();
        assertEquals(Set.of(SEARCHES), after.leftAt(), "and one more asked for is its own");
    }

    /** Each figure the looking holds is told by its own name, and only the ones that ran out. */
    @Test
    void eachFigureTheLookingHoldsIsToldByItsName() {
        LookingForARow looking = new LookingForARow(1);
        LookingForARow.Mark from = looking.from();
        int composed = 0;
        while (looking.composedOnTheWay().spend()) {
            composed++;
        }
        assertEquals(CompositionBudget.ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR.maximum(), composed);
        assertEquals(Set.of(CompositionBudget.ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR), from.leftAt(),
                "the searches, untouched, left nothing");
    }
}
