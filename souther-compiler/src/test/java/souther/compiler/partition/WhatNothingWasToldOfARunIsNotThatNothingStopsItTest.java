package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What the reading of an application told of what a run works out in getting to a relation it
 * states is what the rows of the relation get past. Of a relation it told nothing of, a run may
 * stop on what nothing told: taken for a run that works out nothing, the rows of the relation
 * would be shown computed where no one showed it.
 */
class WhatNothingWasToldOfARunIsNotThatNothingStopsItTest {

    @Test
    void aRelationNothingWasToldOfIsOneAStopMayBeOn() {
        assertSame(UndividedByARelation.Working.UNREAD,
                Cutting.whatWasToldOrNot(_ -> null).apply(null));
    }

    @Test
    void whatWasToldIsWhatTheRowsGetPast() {
        UndividedByARelation.Working told = UndividedByARelation.Working.AS_THE_FORM;
        assertSame(told, Cutting.whatWasToldOrNot(_ -> told).apply(null));
    }

    /** What decided an arm worked out nothing a row gets past, however it came to say so, and
     *  the arm's own working is what a row of it gets past. */
    @Test
    void whatWorkedOutNothingAddsNothingToWhatAnArmWorksOut() {
        UndividedByARelation.Working arm = UndividedByARelation.Working.AS_THE_FORM.notOnEveryRun();
        for (UndividedByARelation.Working decided : List.of(
                UndividedByARelation.Working.AS_THE_FORM,
                UndividedByARelation.Working.NO_STOPS)) {
            assertSame(arm, arm.after(decided));
        }
    }
}
