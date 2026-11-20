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

    /** Working out no operation adds nothing to what a run works out, before it or after it: the
     *  one that told every operation and found none is what leaves the other as it was, whether
     *  the other is read as the form or is an arm's, which is not on every run. */
    @Test
    void whatWorkedOutNoOperationAddsNothingOnEitherSide() {
        UndividedByARelation.Working none = UndividedByARelation.Working.NO_STOPS;
        for (UndividedByARelation.Working working : List.of(
                UndividedByARelation.Working.AS_THE_FORM,
                UndividedByARelation.Working.AS_THE_FORM.notOnEveryRun())) {
            assertSame(working, working.after(none));
            assertSame(working, none.after(working));
        }
    }
}
