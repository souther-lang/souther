package souther.compiler.partition;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
 * positions are read apart. A combination kept so says what kept it ({@link WhyKept}), where no
 * way that was read whole reads it as well. And a behavior with no body has nothing to read
 * ({@link Every}).
 *
 * <p>Not whether either position is worth a combination at all, nor whether two classes can be in
 * one value. Those are {@link BodyDistinction#makesCombinations()}'s and
 * {@link ClassCoexistence}'s, asked beside this and not folded into it.
 */
public sealed interface ReadTogether {

    /** Every combination, which is what a behavior with no body to read is held to. */
    record Every() implements ReadTogether {}

    /**
     * What one way reads together: the classes it admits at each position it reads.
     *
     * <p>The way and not the combinations it makes. Those are the product of what it admits at
     * two positions, which is as large as the two positions' classes make it; held as the way,
     * what is kept grows with the ways and the classes and never with their product, and a
     * combination is asked of it where something counts.
     *
     * @param classes for each position, in the order the reading measured them, the classes the way
     *                reads it in; null where the way does not read it
     * @param apart   for each position, the group of choices of case it is read under a choice at
     *                a time, or -1. Two positions of one group are read together only by the ways
     *                each choice of the group is ({@link CaseChoices}), so this way, which is all
     *                of the choices at once, reads no combination of them
     * @param kept    what the reading could not say of the way, which is why it is read at every
     *                position a row taking it may hold; empty where the way was read whole
     */
    record Way(List<BitSet> classes, List<Integer> apart, Set<WhyKept> kept) {

        public Way {
            List<BitSet> copied = new ArrayList<>();
            for (BitSet each : classes) {
                copied.add(each == null ? null : (BitSet) each.clone());
            }
            classes = Collections.unmodifiableList(copied);
            apart = List.copyOf(apart);
            kept = Collections.unmodifiableSet(new LinkedHashSet<>(kept));
            if (classes.size() != apart.size()) {
                throw new IllegalArgumentException("a way says one thing of each position");
            }
        }

        /** Whether this way reads the {@code one}th and {@code other}th positions together. */
        boolean readsBoth(int one, int other) {
            return classes.get(one) != null && classes.get(other) != null
                    && (apart.get(one) < 0 || !apart.get(one).equals(apart.get(other)));
        }
    }

    /**
     * What the ways a run takes read together, held as the ways.
     *
     * @param axes         the positions, in the order the reading measured them
     * @param classes      each position's classes, in the order of its axis
     * @param ways         each way, once
     * @param everyOneWith the positions every combination of which is read whatever the ways say
     */
    record Read(List<AxisId> axes, List<List<String>> classes, List<Way> ways,
                List<AxisId> everyOneWith) implements ReadTogether {

        public Read {
            axes = List.copyOf(axes);
            classes = classes.stream().<List<String>>map(List::copyOf).toList();
            ways = List.copyOf(ways);
            everyOneWith = List.copyOf(everyOneWith);
            for (Way each : ways) {
                if (each.classes().size() != axes.size()) {
                    throw new IllegalArgumentException("a way is read over the positions measured");
                }
            }
        }
    }

    /**
     * Which classes of {@code other} a run reads with each class of {@code one}, the classes of
     * each named in the order the caller holds them.
     *
     * <p>Asked a class of the first at a time, as the classes of the second a run reads with it, so
     * that what is made to answer is one row of the combinations and not all of them.
     */
    default Between between(AxisId one, List<String> oneClasses, AxisId other,
                            List<String> otherClasses) {
        return switch (this) {
            case Every _ -> Between.every(otherClasses.size());
            case Read it -> {
                int first = it.axes().indexOf(one);
                int second = it.axes().indexOf(other);
                if (first < 0 || second < 0) {
                    throw new IllegalArgumentException("a combination of positions this reading"
                            + " did not measure: " + one + " with " + other);
                }
                Set<WhyKept> everyCombination = new LinkedHashSet<>();
                for (AxisId each : List.of(one, other)) {
                    if (it.everyOneWith().contains(each)) {
                        everyCombination.add(new WhyKept.ARuleNoDecisionReads(each));
                    }
                }
                List<Way> both = new ArrayList<>();
                for (Way each : it.ways()) {
                    if (each.readsBoth(first, second)) {
                        both.add(each);
                    }
                }
                yield new Between.OfTheWays(both, first, second,
                        indexOf(it.classes().get(first), oneClasses, one),
                        positionsOf(it.classes().get(second), otherClasses, other),
                        otherClasses.size(), everyCombination);
            }
        };
    }

    /** For each of {@code asked}, its place among {@code held}. */
    private static int[] indexOf(List<String> held, List<String> asked, AxisId at) {
        Map<String, Integer> place = new HashMap<>();
        for (int index = 0; index < held.size(); index++) {
            place.put(held.get(index), index);
        }
        int[] out = new int[asked.size()];
        for (int index = 0; index < asked.size(); index++) {
            Integer found = place.get(asked.get(index));
            if (found == null) {
                throw new IllegalArgumentException("a class this reading did not measure: "
                        + asked.get(index) + " of " + at);
            }
            out[index] = found;
        }
        return out;
    }

    /** For each of {@code held}, its place among {@code asked}, which names every one of them. */
    private static int[] positionsOf(List<String> held, List<String> asked, AxisId at) {
        if (held.size() != asked.size()) {
            throw new IllegalArgumentException("the classes of " + at + " are asked as "
                    + asked + " and were read as " + held);
        }
        int[] askedAt = indexOf(held, asked, at);
        int[] out = new int[held.size()];
        for (int index = 0; index < askedAt.length; index++) {
            out[askedAt[index]] = index;
        }
        return out;
    }

    /** The combinations of two positions a run reads, a class of the first at a time. */
    sealed interface Between {

        /** The classes of the second a run reads with the {@code oneClass}th of the first, in the
         *  caller's order. */
        BitSet readWith(int oneClass);

        /**
         * Why the {@code oneClass}th class of the first is read with the {@code otherClass}th of
         * the second, where no way read whole reads the two together: what the reading could not
         * say of the ways that do. Empty where a way read whole reads them, and where nothing was
         * read at all.
         */
        Set<WhyKept> keptBy(int oneClass, int otherClass);

        static Between every(int otherClasses) {
            return new All(otherClasses);
        }

        /**
         * Every class of the second with every class of the first, which is what a behavior with no
         * body is held to. Nothing was read to keep any of them, so none says why it is kept.
         */
        record All(int otherClasses) implements Between {

            @Override
            public BitSet readWith(int oneClass) {
                BitSet all = new BitSet(otherClasses);
                all.set(0, otherClasses);
                return all;
            }

            @Override
            public Set<WhyKept> keptBy(int oneClass, int otherClass) {
                return Set.of();
            }
        }

        /** What the ways that read both read, each class of the first against the classes of the
         *  second each such way admits beside it — and every class of the second with every class
         *  of the first where a rule no decision reads divides either position. */
        final class OfTheWays implements Between {

            private final List<Way> ways;
            private final int one;
            private final int other;
            /** For each class of the first as the caller holds them, its place in the reading. */
            private final int[] askedOne;
            /** For each class of the second as the reading holds them, its place among the
             *  caller's. */
            private final int[] heldOther;
            /** For each class of the second as the caller holds them, its place in the reading. */
            private final int[] askedOther;
            private final int otherClasses;
            /** Why every combination is read whatever the ways say, where one is. */
            private final Set<WhyKept> everyCombination;

            OfTheWays(List<Way> ways, int one, int other, int[] askedOne, int[] heldOther,
                      int otherClasses, Set<WhyKept> everyCombination) {
                this.ways = List.copyOf(ways);
                this.one = one;
                this.other = other;
                this.askedOne = askedOne.clone();
                this.heldOther = heldOther.clone();
                this.askedOther = new int[heldOther.length];
                for (int held = 0; held < heldOther.length; held++) {
                    this.askedOther[heldOther[held]] = held;
                }
                this.otherClasses = otherClasses;
                this.everyCombination = Collections.unmodifiableSet(
                        new LinkedHashSet<>(everyCombination));
            }

            @Override
            public Set<WhyKept> keptBy(int oneClass, int otherClass) {
                int at = askedOne[oneClass];
                int there = askedOther[otherClass];
                Set<WhyKept> out = new LinkedHashSet<>(everyCombination);
                for (Way each : ways) {
                    if (each.classes().get(one).get(at) && each.classes().get(other).get(there)) {
                        if (each.kept().isEmpty()) {
                            return Set.of();
                        }
                        out.addAll(each.kept());
                    }
                }
                return out;
            }

            @Override
            public BitSet readWith(int oneClass) {
                BitSet out = new BitSet(otherClasses);
                if (!everyCombination.isEmpty()) {
                    out.set(0, otherClasses);
                    return out;
                }
                int at = askedOne[oneClass];
                for (Way each : ways) {
                    if (!each.classes().get(one).get(at)) {
                        continue;
                    }
                    BitSet there = each.classes().get(other);
                    for (int held = there.nextSetBit(0); held >= 0;
                            held = there.nextSetBit(held + 1)) {
                        out.set(heldOther[held]);
                    }
                }
                return out;
            }
        }
    }
}
