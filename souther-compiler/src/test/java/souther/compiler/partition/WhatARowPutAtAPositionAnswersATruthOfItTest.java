package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.ObservedValue;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a position is true, or holds a value, is read off what a row put there.
 *
 * <p>A row writes a truth at a position as it writes a number, so a statement joining a relation
 * with a truth of the input is one a row can be asked, and a line it draws decides where the row
 * says the truth holds. What a row put nothing at fails, as a relation over a position a row left
 * empty does; what a walk did not reach is not read.
 */
class WhatARowPutAtAPositionAnswersATruthOfItTest {

    private static final TermPath OPEN = TermPath.of("o").then("open");
    private static final TermPath NOTE = TermPath.of("o").then("note");

    private static final Proposition OPEN_HOLDS =
            new Proposition.Truth(new DecisionSubject.AnInput(OPEN), true);
    private static final Proposition A_NOTE_IS_THERE =
            new Proposition.Present(new DecisionSubject.AnInput(NOTE), true);

    @Test
    void aTruthOfThePositionIsAStatementARowAnswers() {
        assertTrue(AStatementAtARow.askable(OPEN_HOLDS));
        assertTrue(AStatementAtARow.askable(A_NOTE_IS_THERE));
        assertTrue(AStatementAtARow.askable(new Proposition.All(List.of(OPEN_HOLDS,
                A_NOTE_IS_THERE.denied()))));
    }

    @Test
    void aTruthHoldsWhereTheRowPutTrueThere() {
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(OPEN_HOLDS, Map.of(OPEN, new ObservedValue.Bool(true))));
        assertEquals(AStatementAtARow.Answer.FAILS,
                at(OPEN_HOLDS, Map.of(OPEN, new ObservedValue.Bool(false))));
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(OPEN_HOLDS.denied(), Map.of(OPEN, new ObservedValue.Bool(false))));
    }

    @Test
    void aValueIsThereWhereTheRowPutOneThere() {
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(A_NOTE_IS_THERE, Map.of(NOTE, new ObservedValue.Text("x"))));
        assertEquals(AStatementAtARow.Answer.FAILS,
                at(A_NOTE_IS_THERE, Map.of(NOTE, new ObservedValue.Absent())));
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(A_NOTE_IS_THERE.denied(), Map.of(NOTE, new ObservedValue.Absent())));
    }

    /** Joined, each part read off its own position, and settled by the one that settles it. */
    @Test
    void joinedEachPartIsReadAtItsOwnPosition() {
        Proposition both = new Proposition.All(List.of(OPEN_HOLDS, A_NOTE_IS_THERE));
        assertEquals(AStatementAtARow.Answer.HOLDS, at(both, Map.of(
                OPEN, new ObservedValue.Bool(true), NOTE, new ObservedValue.Text("x"))));
        assertEquals(AStatementAtARow.Answer.FAILS, at(both, Map.of(
                OPEN, new ObservedValue.Bool(true), NOTE, new ObservedValue.Absent())));
    }

    /** What the walk did not reach is not read, and what is no truth is not one. */
    @Test
    void whatTheRowDoesNotSayIsNotRead() {
        assertEquals(new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK)),
                at(OPEN_HOLDS, Map.of()));
        assertEquals(new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.NO_VALUE)),
                at(OPEN_HOLDS, Map.of(OPEN, new ObservedValue.Integer(1))));
    }

    private static AStatementAtARow.Answer at(Proposition stated,
                                              Map<TermPath, ObservedValue> wrote) {
        return AStatementAtARow.of(stated, "f", null).at(new AnObservationOfAForm() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                ObservedValue value = wrote.get(path);
                return value == null ? WalkResult.couldNotWalk()
                        : WalkResult.reached(new ObservationAtPoint.Value(value));
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a truth of one position is not read over a run");
            }
        });
    }
}
