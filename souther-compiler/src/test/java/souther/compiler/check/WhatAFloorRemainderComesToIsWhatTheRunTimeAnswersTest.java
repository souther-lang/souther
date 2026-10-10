package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.TakenAs;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.ValueName;
import souther.runtime.IntMath;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a remainder is taken of a place as, and what it comes to, is what the run time answers.
 *
 * <p>Held against {@code IntMath.floorMod} and not against a rule written down here: a remainder
 * read off a row and a value written for a remainder both go through the arithmetic this checks, so
 * a second spelling of "takes the sign of the divisor" is a row offered at a number it reads back as
 * something else.
 */
class WhatAFloorRemainderComesToIsWhatTheRunTimeAnswersTest {

    private static final ValueName FLOOR_MOD = new ValueName.Stdlib.Operation("Int", "floorMod");

    private static final List<Long> NUMBERS = List.of(Long.MIN_VALUE, Long.MIN_VALUE + 1, -1001L,
            -100L, -13L, -7L, -3L, -2L, -1L, 0L, 1L, 2L, 3L, 6L, 7L, 8L, 13L, 100L, 1001L,
            Long.MAX_VALUE - 1, Long.MAX_VALUE);

    @Test
    void theRemainderOfEveryPairIsTheOneTheRunTimeAnswers() {
        for (long dividend : NUMBERS) {
            for (long divisor : NUMBERS) {
                if (divisor == 0) {
                    continue;
                }
                ExactAnswer<BigDecimal> remainder = Arithmetic.AFloorRemainder.remainderOf(
                        BigDecimal.valueOf(dividend), BigDecimal.valueOf(divisor));
                assertEquals(BigDecimal.valueOf(IntMath.floorMod(dividend, divisor)),
                        assertInstanceOf(ExactAnswer.Held.class, remainder,
                                dividend + " mod " + divisor).value(),
                        dividend + " mod " + divisor);
            }
        }
    }

    @Test
    void aDivisorOfNoughtIsNotAskedForARemainder() {
        assertThrows(IllegalArgumentException.class, () ->
                Arithmetic.AFloorRemainder.remainderOf(BigDecimal.TEN, BigDecimal.ZERO));
    }

    /** A call is a remainder taken of a place where its divisor reads as a number that is not nought. */
    @Test
    void aCallIsARemainderOfAPlaceWhereItsDivisorIsAConstantAndNotNought() {
        assertInstanceOf(TakenAs.TheFloorRemainder.class, DefaultBoundOperationFacts.get()
                .takenAs(FLOOR_MOD, TakenArguments.at(1, BigDecimal.valueOf(7))));
        assertInstanceOf(TakenAs.TheFloorRemainder.class, DefaultBoundOperationFacts.get()
                .takenAs(FLOOR_MOD, TakenArguments.at(1, BigDecimal.valueOf(-3))));
        assertNull(DefaultBoundOperationFacts.get()
                .takenAs(FLOOR_MOD, TakenArguments.at(1, BigDecimal.ZERO)),
                "nothing is divided by nought: the operation aborts there");
        assertNull(DefaultBoundOperationFacts.get().takenAs(FLOOR_MOD, TakenArguments.NONE),
                "and a divisor the reading has no number for is no period");
    }
}
