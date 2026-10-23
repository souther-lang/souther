package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The bounds a number is left once the numbers after it are eliminated hold at a value of it
 * exactly where some values of the later numbers meet every bound given.
 */
class WhatTheLaterNumbersLeaveIsWhatTheBoundsTogetherLeaveTest {

    private static LaterNumbersEliminated.Bound<String> atMost(long constant,
                                                               Map<String, Long> weights,
                                                               boolean strict) {
        Map<String, ExactRatio> coefs = new HashMap<>();
        weights.forEach((atom, weight) -> coefs.put(atom, ExactRatio.of(weight)));
        return new LaterNumbersEliminated.Bound<>(new LinearForm<>(ExactRatio.of(constant), coefs),
                strict);
    }

    /** Whether every one of {@code bounds} holds with each number at {@code values}. */
    private static boolean holdAt(List<LaterNumbersEliminated.Bound<String>> bounds,
                                  Map<String, ExactRatio> values) {
        for (LaterNumbersEliminated.Bound<String> each : bounds) {
            ExactRatio at = each.form().constant();
            for (Map.Entry<String, ExactRatio> term : each.form().coefs().entrySet()) {
                at = at.plus(term.getValue().times(values.get(term.getKey())).orNull()).orNull();
            }
            if (each.strict() ? at.signum() >= 0 : at.signum() > 0) {
                return false;
            }
        }
        return true;
    }

    /** {@code z + w >= 2}, {@code z + w <= 2}, {@code z - w >= 0} and {@code z - w <= 0}. */
    private static final List<LaterNumbersEliminated.Bound<String>> AT_ONE_EACH = List.of(
            atMost(2, Map.of("z", -1L, "w", -1L), false),
            atMost(-2, Map.of("z", 1L, "w", 1L), false),
            atMost(0, Map.of("z", -1L, "w", 1L), false),
            atMost(0, Map.of("z", 1L, "w", -1L), false));

    @Test
    void boundsOnSumsTheLaterNumberSharesLeaveTheEarlierWhereTheyTogetherDo() {
        LaterNumbersEliminated<String> eliminated =
                LaterNumbersEliminated.of(AT_ONE_EACH, List.of("w", "z"), 4);
        assertFalse(eliminated.noneLeft());
        assertFalse(eliminated.pastThePairs());
        List<LaterNumbersEliminated.Bound<String>> ofW = eliminated.levels().getFirst();
        for (long w = -2; w <= 3; w++) {
            assertEquals(w == 1, holdAt(ofW, Map.of("w", ExactRatio.of(w))), "w = " + w);
        }
        assertEquals(4, eliminated.levels().getLast().size());
        assertTrue(holdAt(eliminated.levels().getLast(),
                Map.of("w", ExactRatio.ONE, "z", ExactRatio.ONE)));
    }

    /** A bound weighing {@code z} below nought and one weighing it above, scaled apart, are
     *  put together so their weights cancel: {@code 2z >= 3w} and {@code z <= 1 - w} leave
     *  {@code w} at two fifths or less. */
    @Test
    void weightsOfEitherSignAndAnyScaleCancel() {
        LaterNumbersEliminated<String> eliminated = LaterNumbersEliminated.of(List.of(
                atMost(0, Map.of("z", -2L, "w", 3L), false),
                atMost(-1, Map.of("z", 1L, "w", 1L), false)), List.of("w", "z"), 1);
        List<LaterNumbersEliminated.Bound<String>> ofW = eliminated.levels().getFirst();
        assertTrue(holdAt(ofW, Map.of("w", new ExactRatio(BigInteger.TWO,
                BigInteger.valueOf(5)))));
        assertFalse(holdAt(ofW, Map.of("w", new ExactRatio(BigInteger.valueOf(3),
                BigInteger.valueOf(7)))));
    }

    /** {@code z < w} and {@code z >= w} leave nothing, which a bound put together at or below
     *  nought rather than below it would not say. */
    @Test
    void aBoundPutTogetherWithAStrictOneIsStrict() {
        assertTrue(LaterNumbersEliminated.of(List.of(
                atMost(0, Map.of("z", 1L, "w", -1L), true),
                atMost(0, Map.of("z", -1L, "w", 1L), false)), List.of("w", "z"), 1).noneLeft());
        assertFalse(LaterNumbersEliminated.of(List.of(
                atMost(0, Map.of("z", 1L, "w", -1L), false),
                atMost(0, Map.of("z", -1L, "w", 1L), false)), List.of("w", "z"), 1).noneLeft());
    }

    /** Eliminating {@code z} takes four pairs. Allowed three, the elimination stops before it and
     *  leaves {@code w} no bound, which says nothing of it. */
    @Test
    void anEliminationTakingMorePairsThanAllowedStopsBeforeIt() {
        LaterNumbersEliminated<String> short3 =
                LaterNumbersEliminated.of(AT_ONE_EACH, List.of("w", "z"), 3);
        assertTrue(short3.pastThePairs());
        assertEquals(0, short3.pairsCombined());
        assertEquals(List.of(), short3.levels().getFirst());
        assertEquals(4, short3.levels().getLast().size());
        LaterNumbersEliminated<String> enough =
                LaterNumbersEliminated.of(AT_ONE_EACH, List.of("w", "z"), 4);
        assertFalse(enough.pastThePairs());
        assertEquals(4, enough.pairsCombined());
    }

    @Test
    void aBoundOfANumberOutsideTheOrderIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> LaterNumbersEliminated.of(AT_ONE_EACH, List.of("z"), 4));
    }
}
