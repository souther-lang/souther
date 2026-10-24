package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way holding the form of a relation to an interval a row beside the relation's line is in is
 * left out of what the terms are read by, and each term is read as the declarations leave it.
 * Which values of a term settle the relation, and which leave it either way, is then what it is
 * with the way — for every value a row has — and no line is drawn between values where one of
 * them has no row.
 *
 * <p>Held here by a walk of every pair of values over a small run, for the way
 * {@code least <= w1 * a + w2 * b <= most} and the relation {@code w1 * a + w2 * b < below}, where
 * the interval reaches as far from the line as the greatest weight: the premise, that a value
 * with a row is classed the same with the way as without it; and what the relation's reading
 * answers for the terms without it, which is that class.
 */
class ATermReadWithoutAWayARowBesideTheLineMeetsIsClassedAsTheWayClassesItTest {

    /** The numbers run from minus this to this. */
    private static final int ENDS = 12;

    /** Where the order of the terms stops, far past anything a sum of them reaches. */
    private static final int TYPE = 1000;

    private static final int[][] WEIGHTS = {{1, 1}, {1, -1}, {-1, 1}, {2, 1}, {1, -2}, {3, 2}};

    private enum Class { TRUE, FALSE, EITHER }

    /** What the relation comes to over the rows with {@code least <= sum <= most}, among the
     *  rows whose first number is {@code value} and the second runs from minus ends to ends: null
     *  where there is none. */
    private static Class walk(int[] weights, int at, int value, int least, int most, int below) {
        boolean holds = false;
        boolean fails = false;
        for (int other = -ENDS; other <= ENDS; other++) {
            int sum = weights[at] * value + weights[1 - at] * other;
            if (sum < least || sum > most) {
                continue;
            }
            holds |= sum < below;
            fails |= sum >= below;
        }
        return !holds && !fails ? null : holds && fails ? Class.EITHER
                : holds ? Class.TRUE : Class.FALSE;
    }

    private static int reach(int[] weights) {
        return Math.max(Math.abs(weights[0]), Math.abs(weights[1]));
    }

    /** Whether the way holds the form on both sides of the line as far as a row beside it
     *  reaches, which is what lets a term be read without it. */
    private static boolean leavesRoom(int[] weights, int least, int most, int below) {
        return least <= below - reach(weights) && most >= below + reach(weights);
    }

    @Test
    void aValueWithARowIsClassedWithTheWayAsWithoutIt() {
        int checked = 0;
        for (int[] weights : WEIGHTS) {
            for (int least = -3 * ENDS; least <= 3 * ENDS; least++) {
                for (int most = least; most <= 3 * ENDS + 6; most += 3) {
                    for (int below = -3 * ENDS; below <= 3 * ENDS; below++) {
                        if (!leavesRoom(weights, least, most, below)) {
                            continue;
                        }
                        for (int at = 0; at < 2; at++) {
                            for (int value = -ENDS; value <= ENDS; value++) {
                                Class with = walk(weights, at, value, least, most, below);
                                if (with != null) {
                                    checked++;
                                    assertEquals(walk(weights, at, value, Integer.MIN_VALUE,
                                                    Integer.MAX_VALUE, below), with,
                                            "weights " + weights[0] + ", " + weights[1] + " from "
                                                    + least + " to " + most + " below " + below
                                                    + " term " + at + " at " + value);
                                }
                            }
                        }
                    }
                }
            }
        }
        assertTrue(checked > 0);
    }

    @Test
    void aWayThatLeavesNoRoomIsNotTheSameAsWithoutIt() {
        // x + y >= 20, x and y from nought to ten, below twenty: the way leaves one sum, twenty,
        // which the relation fails at, so a value it holds the others to settles it.
        int[] sum = {1, 1};
        assertEquals(Class.FALSE, walk(sum, 0, 10, 20, Integer.MAX_VALUE, 20));
        assertEquals(Class.EITHER, walk(sum, 0, 10, Integer.MIN_VALUE, Integer.MAX_VALUE, 20));
        assertTrue(!leavesRoom(sum, 20, Integer.MAX_VALUE, 20));
    }

    private static NumericDomain.Bounds run(long low, long high) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(low)),
                Endpoint.inclusive(Count.of(high)));
    }

    private static WhatARelationLeavesUndivided.Term<String> term(String place, long weight) {
        NumericDomain.Bounds held = run(-ENDS, ENDS);
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight), held,
                held, null, true, Granularity.DISCRETE, run(-TYPE, TYPE));
    }

    /** What the terms are read to leave of {@code value} of the term at {@code at}, or null where
     *  nothing is shown of it. */
    private static Class read(List<WhatARelationLeavesUndivided.Term<String>> terms, int at,
                              int below, int value) {
        WhatARelationLeavesUndivided.Leaves leaves = WhatARelationLeavesUndivided.leavesOf(terms,
                at, ExactRatio.of(-below), Rel.LT, String::equals, (one, other) -> true,
                Granularity.DISCRETE, BigInteger.valueOf(TYPE));
        if (leaves == null) {
            return null;
        }
        if (leaves instanceof WhatARelationLeavesUndivided.Leaves.Settled settled) {
            for (WhatARelationLeavesUndivided.SettledRun each : settled.runs()) {
                boolean after = each.from() == null
                        || each.from().at().compareTo(ExactRatio.of(value)) <= 0;
                boolean before = each.to() == null
                        || each.to().at().compareTo(ExactRatio.of(value)) >= 0;
                if (after && before) {
                    return each.holds() ? Class.TRUE : Class.FALSE;
                }
            }
        }
        return Class.EITHER;
    }

    /**
     * What the relation's reading answers for the terms, which are read without the way, is what a
     * walk says of the values with a row; and a line it draws between two values has a row at
     * each, whatever the way holds the form to beside the line.
     */
    @Test
    void whatTheTermsAreReadToLeaveIsWhatTheWayLeavesAtEveryValueWithARow() {
        int shown = 0;
        for (int[] weights : WEIGHTS) {
            List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                    term("a", weights[0]), term("b", weights[1]));
            for (int below = -3 * ENDS; below <= 3 * ENDS; below++) {
                for (int at = 0; at < 2; at++) {
                    List<Class> read = new ArrayList<>();
                    for (int value = -ENDS; value <= ENDS; value++) {
                        read.add(read(terms, at, below, value));
                    }
                    // The relation's reading is the same whatever the way, so one way is asked
                    // for every line: a sum at least as far below the line as a row beside it
                    // reaches, and none above.
                    int least = below - reach(weights);
                    for (int i = 0; i < read.size(); i++) {
                        int value = i - ENDS;
                        Class here = walk(weights, at, value, least, Integer.MAX_VALUE, below);
                        if (read.get(i) == null || here == null) {
                            continue;
                        }
                        shown++;
                        assertEquals(here, read.get(i), "weights " + weights[0] + ", "
                                + weights[1] + " below " + below + " term " + at + " at " + value);
                        if (i + 1 < read.size() && read.get(i + 1) != null
                                && read.get(i) != read.get(i + 1)) {
                            assertNotNull(walk(weights, at, value, least, Integer.MAX_VALUE,
                                            below),
                                    "a line after " + value + " with no row at it");
                            assertNotNull(walk(weights, at, value + 1, least, Integer.MAX_VALUE,
                                            below),
                                    "a line before " + (value + 1) + " with no row at it");
                        }
                    }
                }
            }
        }
        assertTrue(shown > 0, "some value is shown");
    }
}
