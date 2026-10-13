package souther.compiler.partition;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Which classes of two positions a run of a behavior's body reads together.
 *
 * <p>A combination is worth a row where a run decides something about both positions on its way,
 * in those two classes. Decided on two ways that no run takes both of — {@code usage} read only
 * once the plan is {@code Metered} — the classes of the other way's position answer the same
 * whatever this one is, and a row combining them shows nothing the two rows apart do not. So this
 * is read off the ways a run takes ({@link WhatABodyTellsApart}), a way at a time: what a way
 * admits at one position against what the same way admits at the other, and never what every way
 * admits at one against what every way admits at the other, which is the product this narrows.
 *
 * <p>This narrows the combinations to what the body's present ways read together, and proves
 * nothing about the positions it leaves apart. A {@code Flat} plan whose fee does not turn on usage
 * is what the body says now; a body later made to read usage there is a different body, read again.
 *
 * <p>What the reading could not say stays a combination. A way written without something that
 * holds on it, and a decision whose subject nothing could name, may be about any position; a rule
 * the body wrote that no decision reads tells its position apart where no way shows it. Each of
 * them leaves every combination it may be part of, since what is not read is no proof that two
 * positions are read apart. And a behavior with no body has nothing to read ({@link Every}).
 *
 * <p>Not whether either position is worth a combination at all, nor whether two classes can be in
 * one value. Those are {@link BodyDistinction#makesCombinations()}'s and
 * {@link ClassCoexistence}'s, asked beside this and not folded into it.
 */
public sealed interface ReadTogether {

    /** Every combination, which is what a behavior with no body to read is held to. */
    record Every() implements ReadTogether {}

    /**
     * What the ways a run takes read together, held as one table of classes for each two
     * positions.
     *
     * <p>A table and not the combinations as values: every way writes into it whatever it admits,
     * so the same combination is written many times over, and a table makes each of those a store
     * into a cell rather than a value built and hashed.
     */
    final class Read implements ReadTogether {

        private final List<AxisId> axes;
        private final List<List<String>> classes;
        /** For each two positions, the {@code one}th before the {@code other}th, one cell per
         *  class of the first against each class of the second; null where no way reads both. */
        private final boolean[][] cells;
        private final boolean[] everyOneWith;
        private final Map<AxisId, Integer> at = new HashMap<>();
        private final List<Map<String, Integer>> classAt;

        /**
         * @param axes         the positions, in the order the reading measured them
         * @param classes      each position's classes, in the order of its axis
         * @param cells        for each two positions in that order, as {@link #pair} numbers them,
         *                     whether some way reads each class of the first with each class of the
         *                     second, class of the first major; null where no way reads both
         * @param everyOneWith whether every combination of each position is read whatever the
         *                     ways say
         */
        public Read(List<AxisId> axes, List<List<String>> classes, boolean[][] cells,
                    boolean[] everyOneWith) {
            this.axes = List.copyOf(axes);
            this.classes = classes.stream().<List<String>>map(List::copyOf).toList();
            this.cells = new boolean[cells.length][];
            for (int each = 0; each < cells.length; each++) {
                this.cells[each] = cells[each] == null ? null : cells[each].clone();
            }
            this.everyOneWith = everyOneWith.clone();
            this.classAt = this.classes.stream().map(Read::indexed).toList();
            for (int index = 0; index < this.axes.size(); index++) {
                at.put(this.axes.get(index), index);
            }
        }

        private static Map<String, Integer> indexed(List<String> ids) {
            Map<String, Integer> out = new HashMap<>();
            for (int index = 0; index < ids.size(); index++) {
                out.put(ids.get(index), index);
            }
            return out;
        }

        /** Which table the {@code one}th and {@code other}th positions share, the first before the
         *  second. */
        public static int pair(int one, int other, int positions) {
            return one * positions + other;
        }

        @Override
        public boolean equals(Object other) {
            return this == other || (other instanceof Read it && axes.equals(it.axes)
                    && classes.equals(it.classes) && Arrays.deepEquals(cells, it.cells)
                    && Arrays.equals(everyOneWith, it.everyOneWith));
        }

        @Override
        public int hashCode() {
            return 31 * axes.hashCode() + Arrays.deepHashCode(cells);
        }

        @Override
        public String toString() {
            return "ReadTogether.Read" + axes;
        }
    }

    /** Whether some run reads class {@code oneClass} of {@code one} together with class
     *  {@code otherClass} of {@code other}, or the reading cannot say that none does. */
    default boolean reads(AxisId one, String oneClass, AxisId other, String otherClass) {
        return switch (this) {
            case Every _ -> true;
            case Read it -> {
                Integer first = it.at.get(one);
                Integer second = it.at.get(other);
                if (first == null || second == null) {
                    throw new IllegalArgumentException("a combination of positions this reading"
                            + " did not measure: " + one + " with " + other);
                }
                if (it.everyOneWith[first] || it.everyOneWith[second]) {
                    yield true;
                }
                if (first > second) {
                    yield it.reads(other, otherClass, one, oneClass);
                }
                Integer here = it.classAt.get(first).get(oneClass);
                Integer there = it.classAt.get(second).get(otherClass);
                if (here == null || there == null) {
                    throw new IllegalArgumentException("a class this reading did not measure: "
                            + oneClass + " of " + one + " with " + otherClass + " of " + other);
                }
                boolean[] table = it.cells[Read.pair(first, second, it.axes.size())];
                yield table != null && table[here * it.classes.get(second).size() + there];
            }
        };
    }
}
