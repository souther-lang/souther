package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * The mark of a candidate is taken once for as long as it says nothing, and is what taking it
 * afresh would give after it says something.
 */
class WhatACandidateHasSaidIsMarkedOnceWhileItSaysNothingMoreTest {

    private static Object afresh(Pullback.Trial trial) {
        return ReadingState.snapshotOfFieldsBut(trial, Set.of("marked"));
    }

    @Test
    void aCandidateThatSaysNothingIsMarkedOnce() {
        Pullback.Trial trial = new Pullback.Trial();
        assertSame(trial.mark(), trial.mark());
    }

    @Test
    void whatItSaysAfterBeingMarkedIsInTheNextMark() {
        Pullback.Trial trial = new Pullback.Trial();
        Object before = trial.mark();
        assertEquals(afresh(trial), before);

        trial.restatedAs(() -> null);
        Object afterRestating = trial.mark();
        assertNotEquals(before, afterRestating);
        assertEquals(afresh(trial), afterRestating);

        trial.answersFor(_ -> true);
        Object afterAnswering = trial.mark();
        assertNotEquals(afterRestating, afterAnswering);
        assertEquals(afresh(trial), afterAnswering);
    }
}
