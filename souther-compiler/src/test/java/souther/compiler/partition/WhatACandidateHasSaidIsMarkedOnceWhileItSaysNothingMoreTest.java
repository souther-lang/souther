package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * The mark of a candidate is taken once for as long as it says nothing, and is what taking it
 * afresh would give after it says something, whichever way it says it.
 */
class WhatACandidateHasSaidIsMarkedOnceWhileItSaysNothingMoreTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Object afresh(Pullback.Trial trial) {
        return ReadingState.snapshotOfFieldsBut(trial, Set.of("marked"));
    }

    private static Core number(long value) {
        return new Core.Int(value, Type.INT, POS);
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

    /** The remainders a candidate reads are the third and the fourth of its ways. */
    private static final Set<Integer> REMAINDERS = Set.of(2, 3);

    /** Every way a candidate says something. */
    private static List<Consumer<Pullback.Trial>> waysOfSaying() {
        Relation relation = new Relation.Affine(LinearForm.constant(ExactRatio.ZERO), Rel.GE);
        UndividedByARelation.IntOperation operation = new UndividedByARelation.IntOperation(
                LinearForm.constant(ExactRatio.ZERO), BigInteger.ZERO, BigInteger.ONE, List.of());
        return List.of(
                trial -> trial.says(UndividedByARelation.Working.UNREAD),
                trial -> trial.answersFor(_ -> true),
                trial -> trial.readByTheFormOf(number(1), number(2)),
                trial -> trial.dividendBesideTheRows(number(3), number(4)),
                trial -> trial.landsInAMonth(number(5), operation),
                trial -> trial.restatedAs(() -> null),
                trial -> trial.readOnAnArm(relation,
                        () -> new StopEvidence(UndividedByARelation.Working.UNREAD)),
                trial -> trial.tell(relation, UndividedByARelation.Working.UNREAD));
    }

    @Test
    void whatItSaysBesidesTheRemaindersIsNeitherTheMarkNorTheRemainders() {
        List<Consumer<Pullback.Trial>> ways = waysOfSaying();
        for (int i = 0; i < ways.size(); i++) {
            Pullback.Trial trial = new Pullback.Trial();
            Object before = trial.markBesidesTheRemainders();
            trial.mark();
            assertEquals(before, trial.markBesidesTheRemainders(),
                    "taking the mark is no part of what is said, at way " + i);
            ways.get(i).accept(trial);
            if (REMAINDERS.contains(i)) {
                assertEquals(before, trial.markBesidesTheRemainders(),
                        "a remainder is said beside the rest, at way " + i);
            } else {
                assertNotEquals(before, trial.markBesidesTheRemainders(),
                        "what is said besides the remainders is in it, at way " + i);
            }
        }
    }

    @Test
    void everyWayOfSayingSomethingIsInTheNextMark() {
        List<Consumer<Pullback.Trial>> ways = waysOfSaying();
        for (int i = 0; i < ways.size(); i++) {
            Pullback.Trial trial = new Pullback.Trial();
            Object before = trial.mark();
            ways.get(i).accept(trial);
            Object after = trial.mark();
            assertNotEquals(before, after, "way " + i + " is not in the next mark");
            assertEquals(afresh(trial), after, "way " + i + " is not what a fresh mark says");
        }
    }
}
