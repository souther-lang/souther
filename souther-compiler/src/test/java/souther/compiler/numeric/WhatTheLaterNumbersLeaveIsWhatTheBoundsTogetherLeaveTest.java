package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

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

    /**
     * What bounds on the numbers up to the first {@code keep} leave them once the others are
     * eliminated, every bound below put with every bound above and nothing scaled, skipped or
     * counted — or null where a bound of no number fails.
     */
    private static List<LaterNumbersEliminated.Bound<String>> projected(
            List<LaterNumbersEliminated.Bound<String>> bounds, List<String> order, int keep) {
        List<LaterNumbersEliminated.Bound<String>> now = bounds;
        for (int place = order.size() - 1; place > keep; place--) {
            String number = order.get(place);
            List<LaterNumbersEliminated.Bound<String>> next = new ArrayList<>();
            List<LaterNumbersEliminated.Bound<String>> ups = new ArrayList<>();
            List<LaterNumbersEliminated.Bound<String>> downs = new ArrayList<>();
            for (LaterNumbersEliminated.Bound<String> each : now) {
                ExactRatio weight = each.form().coefs().get(number);
                (weight == null ? next : weight.signum() > 0 ? ups : downs).add(each);
            }
            for (LaterNumbersEliminated.Bound<String> up : ups) {
                for (LaterNumbersEliminated.Bound<String> down : downs) {
                    LinearForm<String> scaledUp = up.form()
                            .times(down.form().coefs().get(number).negated()).orNull();
                    LinearForm<String> scaledDown = down.form()
                            .times(up.form().coefs().get(number)).orNull();
                    next.add(new LaterNumbersEliminated.Bound<>(
                            scaledUp.plus(scaledDown).orNull(), up.strict() || down.strict()));
                }
            }
            now = next;
        }
        for (LaterNumbersEliminated.Bound<String> each : now) {
            if (each.form().coefs().isEmpty() && !holdAt(List.of(each), Map.of())) {
                return null;
            }
        }
        return now;
    }

    private static LaterNumbersEliminated.Bound<String> randomBound(Random random) {
        Map<String, Long> weights = new HashMap<>();
        for (String number : List.of("x", "y", "z")) {
            long weight = random.nextInt(5) - 2L;
            if (weight != 0) {
                weights.put(number, weight);
            }
        }
        return atMost(random.nextInt(7) - 3L, weights, random.nextBoolean());
    }

    /**
     * The contract, against an elimination that does none of what this one saves work by: over
     * small systems of a few bounds on three numbers, no values meet them exactly where the
     * naive elimination finds a bound of no number failing, and the bounds at each level together
     * hold at the values of the numbers up to it exactly where the naive elimination of the numbers
     * after it leaves them. An elimination stopped short has reached the levels the whole one has,
     * and no more pairs than it was allowed.
     */
    @Test
    void anEliminationLeavesWhatTheNaiveEliminationLeavesAndStopsShortAtTheLevelsItReached() {
        List<String> order = List.of("x", "y", "z");
        Random random = new Random(2693);
        int none = 0;
        int stopped = 0;
        for (int each = 0; each < 3000; each++) {
            List<LaterNumbersEliminated.Bound<String>> bounds = new ArrayList<>();
            for (int count = 1 + random.nextInt(6); count > 0; count--) {
                bounds.add(randomBound(random));
            }
            LaterNumbersEliminated<String> whole = LaterNumbersEliminated.of(bounds, order, 1000);
            String said = bounds.toString();
            if (projected(bounds, order, -1) == null) {
                assertInstanceOf(LaterNumbersEliminated.NoneLeft.class, whole, said);
                none++;
                continue;
            }
            List<List<LaterNumbersEliminated.Bound<String>>> levels = levels(whole);
            for (int place = 0; place < order.size(); place++) {
                List<LaterNumbersEliminated.Bound<String>> naive = projected(bounds, order, place);
                List<LaterNumbersEliminated.Bound<String>> together = new ArrayList<>();
                levels.subList(0, place + 1).forEach(together::addAll);
                for (int at = 0; at < Math.pow(5, place + 1); at++) {
                    Map<String, ExactRatio> values = new HashMap<>();
                    int rest = at;
                    for (int number = 0; number <= place; number++) {
                        values.put(order.get(number), ExactRatio.of(rest % 5 - 2L));
                        rest /= 5;
                    }
                    assertEquals(holdAt(naive, values), holdAt(together, values),
                            said + " at " + values);
                }
            }
            for (long allowed = 0; allowed < whole.pairsCombined(); allowed++) {
                LaterNumbersEliminated<String> cut =
                        LaterNumbersEliminated.of(bounds, order, allowed);
                assertTrue(cut.pairsCombined() <= allowed, said);
                if (cut instanceof LaterNumbersEliminated.StoppedShort<String> reached) {
                    assertEquals(LaterNumbersEliminated.Why.PAIRS, reached.why(), said);
                    assertEquals(levels.subList(reached.place(), levels.size()), reached.reached(),
                            said);
                    stopped++;
                }
            }
        }
        assertTrue(none > 0);
        assertTrue(stopped > 0);
    }

    /**
     * Bounds of one number alone are compared as they are written, so that the tightest is the
     * tightest however far the weights of the bounds are apart: {@code z <= -T²} (written
     * {@code z/T + T <= 0}) and {@code z >= -T²/2} leave none for a {@code T} whose square no
     * ratio holds.
     */
    @Test
    void boundsOfTheNumberAloneAreComparedWithoutDividingThemThroughToWeighOne() {
        ExactRatio t = new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MAX_VALUE / 2 + 1, 0);
        ExactRatio over = new ExactRatio(BigInteger.ONE, BigInteger.ONE,
                -(Long.MAX_VALUE / 2 + 1), 0);
        ExactRatio twiceT = t.times(ExactRatio.of(2)).orNull();
        ExactRatio fourOver = over.times(ExactRatio.of(4)).orNull();
        LaterNumbersEliminated.Bound<String> first = new LaterNumbersEliminated.Bound<>(
                new LinearForm<>(t, Map.of("z", over)), false);
        LaterNumbersEliminated.Bound<String> second = new LaterNumbersEliminated.Bound<>(
                new LinearForm<>(twiceT, Map.of("z", fourOver)), false);
        LaterNumbersEliminated.Bound<String> third = new LaterNumbersEliminated.Bound<>(
                new LinearForm<>(twiceT.negated(), Map.of("z", fourOver.negated())), false);
        assertInstanceOf(LaterNumbersEliminated.NoneLeft.class, LaterNumbersEliminated.of(
                List.of(first, second, third), List.of("w", "z"), 0));
    }

    /** Two bounds of one number alone whose weights and constants cannot be set beside each
     *  other are an arithmetic that stopped it, not a bound taken as it stands. */
    @Test
    void boundsOfTheNumberAloneBeyondTheArithmeticStopItForThat() {
        // The second cannot be divided through by its weight, and set beside the first as it is
        // written, its weight times the first's constant has no ratio either.
        ExactRatio far = new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MAX_VALUE, 0);
        ExactRatio near = new ExactRatio(BigInteger.ONE, BigInteger.ONE, -5, 0);
        LaterNumbersEliminated.StoppedShort<?> stopped = assertInstanceOf(
                LaterNumbersEliminated.StoppedShort.class, LaterNumbersEliminated.of(List.of(
                        new LaterNumbersEliminated.Bound<>(
                                new LinearForm<>(ExactRatio.of(2), Map.of("z", ExactRatio.ONE)),
                                false),
                        new LaterNumbersEliminated.Bound<>(
                                new LinearForm<>(near, Map.of("z", far)), false)),
                        List.of("w", "z"), 0));
        assertEquals(LaterNumbersEliminated.Why.ARITHMETIC, stopped.why());
        assertEquals(1, stopped.place());
    }

    /**
     * The pairs put together are the pairs of which at least one is not of the number alone, and
     * those are all that are counted: three of the number alone each way and two bounds of other
     * numbers above it and one below take three, six and two.
     */
    @Test
    void theOnlyPairsPutTogetherAreThoseNotBothOfTheNumberAlone() {
        List<LaterNumbersEliminated.Bound<String>> bounds = List.of(
                atMost(-10, Map.of("z", 1L), false), atMost(-11, Map.of("z", 1L), false),
                atMost(-12, Map.of("z", 1L), false), atMost(-10, Map.of("z", -1L), false),
                atMost(-11, Map.of("z", -1L), false), atMost(-12, Map.of("z", -1L), false),
                atMost(-5, Map.of("z", 1L, "w", 1L), false),
                atMost(-9, Map.of("z", 1L, "w", 2L), false),
                atMost(-3, Map.of("z", -1L, "w", 1L), false));
        assertEquals(11, LaterNumbersEliminated.of(bounds, List.of("w", "z"), 11).pairsCombined());
        assertEquals(LaterNumbersEliminated.Why.PAIRS, assertInstanceOf(
                LaterNumbersEliminated.StoppedShort.class,
                LaterNumbersEliminated.of(bounds, List.of("w", "z"), 10)).why());
    }

    @Test
    void aBoundOfANumberOutsideTheOrderIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> LaterNumbersEliminated.of(AT_ONE_EACH, List.of("z"), 4));
    }
}
