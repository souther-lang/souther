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

/**
 * What a candidate has said ({@link Pullback.Trial#mark}) moves with every way it says something,
 * and what it has said besides the remainders it read moves with every way but those.
 *
 * <p>A reading must leave the candidate it is read under as it found it, and a remainder read
 * again is taken where the candidate has said nothing else: a way of saying something that moves
 * neither would let a reading that said it be taken where it would not be the same.
 */
class WhatACandidateHasSaidMovesWithEveryWayOfSayingItTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Core number(long value) {
        return new Core.Int(value, Type.INT, POS);
    }

    @Test
    void aCandidateThatSaysNothingMoreIsMarkedTheSame() {
        Pullback.Trial trial = new Pullback.Trial();
        assertEquals(trial.mark(), trial.mark());
        assertEquals(trial.mark().hashCode(), trial.mark().hashCode());
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
                trial -> trial.readOnAnArm(new Pullback.ArmRead.OfARelation(relation),
                        new Pullback.OnThisArm(() ->
                        AffineReading.WorkedOut.ofWhatIsToldOf(UndividedByARelation.Working.UNREAD),
                        () -> UndividedByARelation.Working.NOTHING, List.of())),
                trial -> trial.tell(relation, UndividedByARelation.Working.UNREAD));
    }

    @Test
    void everyWayOfSayingSomethingMovesTheMark() {
        List<Consumer<Pullback.Trial>> ways = waysOfSaying();
        for (int i = 0; i < ways.size(); i++) {
            Pullback.Trial trial = new Pullback.Trial();
            Object before = trial.mark();
            ways.get(i).accept(trial);
            assertNotEquals(before, trial.mark(), "way " + i + " is not in the next mark");
        }
    }

    @Test
    void whatItSaysBesidesTheRemaindersMovesWithEveryWayButTheRemainders() {
        List<Consumer<Pullback.Trial>> ways = waysOfSaying();
        for (int i = 0; i < ways.size(); i++) {
            Pullback.Trial trial = new Pullback.Trial();
            Object before = trial.markBesidesTheRemainders();
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

    /**
     * A remainder read under one candidate is taken under another where neither said anything
     * besides remainders; where one has said something, it is taken only under that candidate
     * while it says nothing more.
     */
    @Test
    void candidatesThatSaidNothingButRemaindersHaveSaidTheSameAndOthersHaveNot() {
        Pullback.Trial one = new Pullback.Trial();
        Pullback.Trial other = new Pullback.Trial();
        other.readByTheFormOf(number(1), number(2));
        assertEquals(one.markBesidesTheRemainders(), other.markBesidesTheRemainders());

        one.says(UndividedByARelation.Working.UNREAD);
        other.says(UndividedByARelation.Working.UNREAD);
        assertNotEquals(one.markBesidesTheRemainders(), other.markBesidesTheRemainders(),
                "what another candidate said is not compared with it");
        assertEquals(one.markBesidesTheRemainders(), one.markBesidesTheRemainders());
    }
}
