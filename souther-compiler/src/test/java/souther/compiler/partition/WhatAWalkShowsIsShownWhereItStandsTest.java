package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.KeyedAccumulation;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a walk that files under each key shows of its step is shown where the operations stand in
 * that step, and not wherever the same node is met. {@code Core} does not refuse a node standing
 * at two places, and the nodes this compiler emits never alias today, so this is built by hand:
 * what is held here is that the walk's proof does not depend on that.
 *
 * <p>The step of a walk is shown what the walk shows, and its seed and what it walks nothing. An
 * operation that files is shown to stop no run where it stands, and its move only under the
 * argument it moves by: the same move met under another argument of it, under another operation,
 * or anywhere else is not shown.
 */
class WhatAWalkShowsIsShownWhereItStandsTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Core node(long n) {
        return new Core.Int(n, Type.INT, POS);
    }

    private final Core operation = node(1);
    private final Core movedBy = node(2);
    private final Core move = node(3);
    private final Core key = node(4);
    private final Core step = node(5);
    private final Core seed = node(6);

    private final Pullback.ShownByAWalk ofTheStep = new Pullback.ShownByAWalk(
            List.of(new KeyedAccumulation.Filing(operation, movedBy, move)),
            List.of(operation), null);

    @Test
    void theStepIsShownWhatTheWalkShowsAndTheRestNothing() {
        assertEquals(ofTheStep, Pullback.ShownByAWalk.inTheWalk(step, ofTheStep, step));
        assertEquals(Pullback.ShownByAWalk.NOTHING,
                Pullback.ShownByAWalk.inTheWalk(step, ofTheStep, seed));
    }

    @Test
    void anOperationThatFilesIsShownWhereItStandsAndItsMoveIsNot() {
        assertTrue(ofTheStep.stopsNoRunAt(operation));
        assertFalse(ofTheStep.stopsNoRunAt(move),
                "the move is shown only under the argument it moves by");
    }

    @Test
    void theMoveIsShownUnderTheArgumentItMovesByAndNowhereElse() {
        Pullback.ShownByAWalk underTheArgument = ofTheStep.under(operation, movedBy);
        assertTrue(underTheArgument.stopsNoRunAt(move));
        assertFalse(underTheArgument.stopsNoRunAt(operation),
                "the operation that files is not shown again under its own argument");
        assertEquals(Pullback.ShownByAWalk.NOTHING, ofTheStep.under(operation, key),
                "under another argument of the operation, nothing is shown");
        assertFalse(ofTheStep.under(key, move).stopsNoRunAt(move),
                "the same move met under another node is not shown");
    }

    @Test
    void whatIsShownGoesDownThroughWhatIsNoFilingAndNothingIsShownOfNothing() {
        assertEquals(ofTheStep, ofTheStep.under(key, seed));
        assertFalse(Pullback.ShownByAWalk.NOTHING.stopsNoRunAt(operation));
        assertFalse(Pullback.ShownByAWalk.NOTHING.stopsNoRunAt(move));
    }
}
