package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.Arrays;
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
 * <p>Held here by a walk of every row over small runs, for the way
 * {@code least <= w1 * a + w2 * b} and the relation {@code w1 * a + w2 * b < below}, where the
 * interval reaches as far from the line as the greatest weight: the premise, that a value with a
 * row is classed the same with the way as without it; what the relation's reading answers for the
 * terms without it, which is that class, and that it answers for every value with a row where the
 * terms are weighed one and minus one; and, over three terms, that two of them the rest of the
 * way holds to one another are not read as though each could stand where the other does not.
 */
class ATermReadWithoutAWayARowBesideTheLineMeetsIsClassedAsTheWayClassesItTest {

    /** The numbers run from minus this to this. */
    private static final int ENDS = 12;

    /** Where the order of the terms stops, far past anything a sum of them reaches. */
    private static final int TYPE = 1000;

    private static final int[][] WEIGHTS = {{1, 1}, {1, -1}, {-1, 1}, {2, 1}, {1, -2}, {3, 2}};

    private static final int[][] UNIT_WEIGHTS = {{1, 1}, {1, -1}, {-1, 1}};

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
        int greatest = 0;
        for (int each : weights) {
            greatest = Math.max(greatest, Math.abs(each));
        }
        return greatest;
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

    private static WhatARelationLeavesUndivided.Term<String> term(String place, long weight,
                                                                 int low, int high) {
        NumericDomain.Bounds held = run(low, high);
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight), held,
                held, null, true, Granularity.DISCRETE, run(-TYPE, TYPE));
    }

    /** What the terms are read to leave of the term at {@code at}, or null where nothing is
     *  shown of it. */
    private static WhatARelationLeavesUndivided.Leaves leaves(
            List<WhatARelationLeavesUndivided.Term<String>> terms, int at, int below,
            WhatARelationLeavesUndivided.Independence independent) {
        return WhatARelationLeavesUndivided.leavesOf(terms, at, ExactRatio.of(-below), Rel.LT,
                String::equals, independent, Granularity.DISCRETE, BigInteger.valueOf(TYPE));
    }

    /** What {@code leaves} says of {@code value}: null where nothing is shown. */
    private static Class classOf(WhatARelationLeavesUndivided.Leaves leaves, int value) {
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
                    term("a", weights[0], -ENDS, ENDS), term("b", weights[1], -ENDS, ENDS));
            for (int below = -3 * ENDS; below <= 3 * ENDS; below++) {
                // The relation's reading is the same whatever the way, so one way is asked
                // for every line: a sum at least as far below the line as a row beside it
                // reaches, and none above.
                int least = below - reach(weights);
                for (int at = 0; at < 2; at++) {
                    WhatARelationLeavesUndivided.Leaves leaves = leaves(terms, at, below,
                            (one, other) -> true);
                    for (int value = -ENDS; value <= ENDS; value++) {
                        Class read = classOf(leaves, value);
                        Class here = walk(weights, at, value, least, Integer.MAX_VALUE, below);
                        if (read == null || here == null) {
                            continue;
                        }
                        shown++;
                        assertEquals(here, read, "weights " + weights[0] + ", " + weights[1]
                                + " below " + below + " term " + at + " at " + value);
                        Class next = classOf(leaves, value + 1);
                        if (value < ENDS && next != null && read != next) {
                            assertNotNull(here, "a line after " + value + " with no row at it");
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

    /**
     * Where the terms are weighed one and minus one, a value with a row is read: the terms are
     * read without the way for the lines of the relation, and one value of a term that has a row
     * and is not shown is a line the reading would miss.
     */
    @Test
    void everyValueWithARowIsReadWhereTheTermsAreWeighedOneAndMinusOne() {
        for (int[] weights : UNIT_WEIGHTS) {
            List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                    term("a", weights[0], -ENDS, ENDS), term("b", weights[1], -ENDS, ENDS));
            for (int below = -2 * ENDS; below <= 2 * ENDS; below++) {
                int least = below - reach(weights);
                for (int at = 0; at < 2; at++) {
                    WhatARelationLeavesUndivided.Leaves leaves = leaves(terms, at, below,
                            (one, other) -> true);
                    for (int value = -ENDS; value <= ENDS; value++) {
                        if (walk(weights, at, value, least, Integer.MAX_VALUE, below) != null) {
                            assertNotNull(classOf(leaves, value), "weights " + weights[0] + ", "
                                    + weights[1] + " below " + below + " term " + at + " at "
                                    + value + " has a row and is not read");
                        }
                    }
                }
            }
        }
    }

    /** What the relation comes to over the rows of three numbers from {@code runs}, two of which
     *  are held equal, that hold the sum at {@code least} or more, among those whose number at
     *  {@code at} is {@code value}; null where there is none. */
    private static Class walkThree(int[][] runs, int[] tied, int at, int value, int least,
                                   int below) {
        boolean holds = false;
        boolean fails = false;
        for (int a = runs[0][0]; a <= runs[0][1]; a++) {
            for (int b = runs[1][0]; b <= runs[1][1]; b++) {
                for (int c = runs[2][0]; c <= runs[2][1]; c++) {
                    int[] row = {a, b, c};
                    int sum = a + b + c;
                    if (row[at] != value || row[tied[0]] != row[tied[1]] || sum < least) {
                        continue;
                    }
                    holds |= sum < below;
                    fails |= sum >= below;
                }
            }
        }
        return !holds && !fails ? null : holds && fails ? Class.EITHER
                : holds ? Class.TRUE : Class.FALSE;
    }

    /**
     * Two of three terms the way holds equal to each other are tied, and neither is read as a term
     * that stands where it may whatever the other is: {@code a + b + c < 0} after
     * {@code a + b + c >= -1}, {@code b} and {@code c} from minus one to nought and equal, has
     * {@code a} at nought below the line at no row, and the terms are read without the sum's
     * statement but not without the equality.
     */
    @Test
    void twoTermsTheRestOfTheWayHoldsToEachOtherAreNotReadAsFree() {
        int[][][] allRuns = {{{-4, 4}, {-1, 0}, {-1, 0}}, {{-1, 0}, {-4, 4}, {-1, 0}},
                {{-3, 3}, {-3, 3}, {-3, 3}}, {{-2, 2}, {-1, 1}, {0, 3}}};
        int[][] allTied = {{1, 2}, {0, 1}, {0, 2}};
        int shown = 0;
        for (int[][] runs : allRuns) {
            List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                    term("a", 1, runs[0][0], runs[0][1]), term("b", 1, runs[1][0], runs[1][1]),
                    term("c", 1, runs[2][0], runs[2][1]));
            for (int[] tied : allTied) {
                WhatARelationLeavesUndivided.Independence independent = (one, other) ->
                        !(Math.min(one, other) == tied[0] && Math.max(one, other) == tied[1]);
                for (int below = -6; below <= 6; below++) {
                    int least = below - 1;
                    for (int at = 0; at < 3; at++) {
                        WhatARelationLeavesUndivided.Leaves leaves = leaves(terms, at, below,
                                independent);
                        for (int value = runs[at][0]; value <= runs[at][1]; value++) {
                            Class read = classOf(leaves, value);
                            Class here = walkThree(runs, tied, at, value, least, below);
                            if (read == null || here == null) {
                                continue;
                            }
                            shown++;
                            assertEquals(here, read, "runs " + Arrays.deepToString(runs)
                                    + " tied " + tied[0] + ", " + tied[1] + " below " + below
                                    + " term " + at + " at " + value);
                        }
                    }
                }
            }
        }
        assertTrue(shown > 0, "some value is shown");
    }
}
