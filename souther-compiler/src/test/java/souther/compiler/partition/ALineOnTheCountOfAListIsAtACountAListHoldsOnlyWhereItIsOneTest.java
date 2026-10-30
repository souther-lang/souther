package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The line a comparison draws on the count of a list is at a count a list holds only where the
 * form of the whole comparison is that count and a constant: the line is then one count whatever
 * the rest of the input is, and it and the count above it are counts of a list.
 */
class ALineOnTheCountOfAListIsAtACountAListHoldsOnlyWhereItIsOneTest {

    private static final NumericTerm COUNT = new NumericTerm.ValueOf(TermPath.of("found"));
    private static final NumericTerm OTHER = new NumericTerm.ValueOf(TermPath.of("contacts"));

    /** {@code weight * count + constant}. */
    private static LinearForm<NumericTerm> form(long weight, long constant) {
        return LinearForm.weighing(COUNT, ExactRatio.of(weight))
                .plus(LinearForm.constant(ExactRatio.of(constant))).orNull();
    }

    private static boolean holds(LinearForm<NumericTerm> whole) {
        return AffineReading.WhatLiesBesideTheStop.lineIsAtACountAListHolds(whole, COUNT);
    }

    @Test
    void theSameLineIsAtACountHoweverTheFormIsScaledAndMoved() {
        assertTrue(holds(form(1, -1)));
        assertTrue(holds(form(2, -2)));
        assertTrue(holds(form(-1, 1)));
        assertTrue(holds(form(1, 0)));
    }

    @Test
    void aLineBelowNoughtOrOffTheWholeNumbersIsAtNoCountAListHolds() {
        assertFalse(holds(form(1, 99)));
        assertFalse(holds(form(2, -3)));
    }

    @Test
    void theLineAtTheGreatestCountIsPastTheCountAboveIt() {
        assertTrue(holds(form(1, -(Integer.MAX_VALUE - 1L))));
        assertFalse(holds(form(1, -(long) Integer.MAX_VALUE)));
    }

    @Test
    void aFormWithAnotherNumberInItIsALineThatMovesWithTheInput() {
        LinearForm<NumericTerm> moves = form(1, -1)
                .plus(LinearForm.atom(OTHER)).orNull();
        assertFalse(holds(moves));
        assertFalse(holds(LinearForm.atom(OTHER)));
        assertFalse(holds(null));
    }
}
