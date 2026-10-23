package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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

    private static List<List<LaterNumbersEliminated.Bound<String>>> levels(
            LaterNumbersEliminated<String> eliminated) {
        assertInstanceOf(LaterNumbersEliminated.Eliminated.class, eliminated);
        return ((LaterNumbersEliminated.Eliminated<String>) eliminated).levels();
    }

    /** {@code z + w >= 2}, {@code z + w <= 2}, {@code z - w >= 0} and {@code z - w <= 0}. */
    private static final List<LaterNumbersEliminated.Bound<String>> AT_ONE_EACH = List.of(
            atMost(2, Map.of("z", -1L, "w", -1L), false),
            atMost(-2, Map.of("z", 1L, "w", 1L), false),
            atMost(0, Map.of("z", -1L, "w", 1L), false),
            atMost(0, Map.of("z", 1L, "w", -1L), false));

    @Test
    void boundsOnSumsTheLaterNumberSharesLeaveTheEarlierWhereTheyTogetherDo() {
        List<List<LaterNumbersEliminated.Bound<String>>> levels =
                levels(LaterNumbersEliminated.of(AT_ONE_EACH, List.of("w", "z"), 4));
        for (long w = -2; w <= 3; w++) {
            assertEquals(w == 1, holdAt(levels.getFirst(), Map.of("w", ExactRatio.of(w))),
                    "w = " + w);
        }
        assertEquals(4, levels.getLast().size());
        assertTrue(holdAt(levels.getLast(), Map.of("w", ExactRatio.ONE, "z", ExactRatio.ONE)));
    }

    /** A bound weighing {@code z} below nought and one weighing it above, scaled apart, are
     *  put together so their weights cancel: {@code 2z >= 3w} and {@code z <= 1 - w} leave
     *  {@code w} at two fifths or less. */
    @Test
    void weightsOfEitherSignAndAnyScaleCancel() {
        List<LaterNumbersEliminated.Bound<String>> ofW = levels(LaterNumbersEliminated.of(List.of(
                atMost(0, Map.of("z", -2L, "w", 3L), false),
                atMost(-1, Map.of("z", 1L, "w", 1L), false)), List.of("w", "z"), 1)).getFirst();
        assertTrue(holdAt(ofW, Map.of("w", new ExactRatio(BigInteger.TWO,
                BigInteger.valueOf(5)))));
        assertFalse(holdAt(ofW, Map.of("w", new ExactRatio(BigInteger.valueOf(3),
                BigInteger.valueOf(7)))));
    }

    /** {@code z < w} and {@code z >= w} leave nothing, which a bound put together at or below
     *  nought rather than below it would not say. */
    @Test
    void aBoundPutTogetherWithAStrictOneIsStrict() {
        assertInstanceOf(LaterNumbersEliminated.NoneLeft.class, LaterNumbersEliminated.of(List.of(
                atMost(0, Map.of("z", 1L, "w", -1L), true),
                atMost(0, Map.of("z", -1L, "w", 1L), false)), List.of("w", "z"), 1));
        assertInstanceOf(LaterNumbersEliminated.Eliminated.class, LaterNumbersEliminated.of(
                List.of(atMost(0, Map.of("z", 1L, "w", -1L), false),
                        atMost(0, Map.of("z", -1L, "w", 1L), false)), List.of("w", "z"), 1));
    }

    /** Eliminating {@code z} takes four pairs. Allowed three, the elimination stops before it,
     *  says so, and says nothing of {@code w}. */
    @Test
    void anEliminationTakingMorePairsThanAllowedStopsBeforeIt() {
        LaterNumbersEliminated.StoppedShort<?> stopped = assertInstanceOf(
                LaterNumbersEliminated.StoppedShort.class,
                LaterNumbersEliminated.of(AT_ONE_EACH, List.of("w", "z"), 3));
        assertEquals(LaterNumbersEliminated.Why.PAIRS, stopped.why());
        assertEquals(1, stopped.place());
        assertEquals(1, stopped.reached().size());
        assertEquals(4, stopped.reached().getFirst().size());
        assertEquals(0, stopped.pairsCombined());
        assertEquals(4, LaterNumbersEliminated.of(AT_ONE_EACH, List.of("w", "z"), 4)
                .pairsCombined());
    }

    /**
     * A bound below a number and one above it that are both of it alone leave no bound of another,
     * and take no pairs: numbers between ends of their own each are eliminated with none, and a
     * number with ends of its own and one bound beside another takes only the pairs with that one.
     */
    @Test
    void boundsOfTheNumberAloneAreNotPutTogether() {
        List<LaterNumbersEliminated.Bound<String>> ends = List.of(
                atMost(0, Map.of("z", -1L), false), atMost(-5, Map.of("z", 1L), false),
                atMost(1, Map.of("w", -1L), false), atMost(-2, Map.of("w", 1L), false));
        assertEquals(0, LaterNumbersEliminated.of(ends, List.of("w", "z"), 0).pairsCombined());
        List<LaterNumbersEliminated.Bound<String>> beside = List.of(
                atMost(0, Map.of("z", -1L), false), atMost(-5, Map.of("z", 1L), false),
                atMost(-3, Map.of("z", 1L, "w", 1L), false));
        LaterNumbersEliminated<String> eliminated =
                LaterNumbersEliminated.of(beside, List.of("w", "z"), 1);
        assertEquals(1, eliminated.pairsCombined());
        assertTrue(holdAt(levels(eliminated).getFirst(), Map.of("w", ExactRatio.of(3))));
        assertFalse(holdAt(levels(eliminated).getFirst(), Map.of("w", ExactRatio.of(4))));
    }

    /**
     * Bounds of one number alone are not put together pair by pair, and still say when no value
     * meets them: the tightest below and the tightest above are set beside each other, whichever
     * place the number has and however many bounds are there.
     */
    @Test
    void boundsOfTheNumberAloneThatNoValueMeetsLeaveNoneLeft() {
        for (String number : List.of("z", "w")) {
            assertInstanceOf(LaterNumbersEliminated.NoneLeft.class, LaterNumbersEliminated.of(
                    List.of(atMost(0, Map.of(number, 1L), false),
                            atMost(1, Map.of(number, -1L), false)), List.of("w", "z"), 0), number);
        }
        assertInstanceOf(LaterNumbersEliminated.NoneLeft.class, LaterNumbersEliminated.of(List.of(
                atMost(-5, Map.of("z", 1L), false), atMost(0, Map.of("z", 1L), false),
                atMost(1, Map.of("z", -1L), false), atMost(-3, Map.of("z", -1L), false)),
                List.of("w", "z"), 0));
    }

    /** {@code z <= 1} and {@code z > 1} leave nothing, and {@code z >= 1} leaves one. */
    @Test
    void boundsOfTheNumberAloneMeetingAtAValueLeaveNoneOnlyWhereOneIsStrict() {
        assertInstanceOf(LaterNumbersEliminated.NoneLeft.class, LaterNumbersEliminated.of(List.of(
                atMost(-1, Map.of("z", 1L), false), atMost(1, Map.of("z", -1L), true)),
                List.of("w", "z"), 0));
        assertInstanceOf(LaterNumbersEliminated.Eliminated.class, LaterNumbersEliminated.of(
                List.of(atMost(-1, Map.of("z", 1L), false), atMost(1, Map.of("z", -1L), false)),
                List.of("w", "z"), 0));
    }

    /** Only the pairs put together are counted: the first of two that {@code z <= w} and
     *  {@code z >= w + 1} are put together with is already none. */
    @Test
    void aPairIsCountedOnlyOnceItIsPutTogether() {
        LaterNumbersEliminated<String> none = LaterNumbersEliminated.of(List.of(
                atMost(0, Map.of("z", 1L, "w", -1L), false),
                atMost(1, Map.of("z", -1L, "w", 1L), false),
                atMost(-5, Map.of("z", 1L, "w", 1L), false)), List.of("w", "z"), 4);
        assertInstanceOf(LaterNumbersEliminated.NoneLeft.class, none);
        assertEquals(1, none.pairsCombined());
    }

    @Test
    void aBoundOfANumberOutsideTheOrderIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> LaterNumbersEliminated.of(AT_ONE_EACH, List.of("z"), 4));
    }
}
