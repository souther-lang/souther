package souther.compiler.partition;

import org.junit.jupiter.api.Test;

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
        UndividedByARelation.Working told = UndividedByARelation.Working.NOTHING;
        assertSame(told, Cutting.whatWasToldOrNot(_ -> told).apply(null));
    }
}
