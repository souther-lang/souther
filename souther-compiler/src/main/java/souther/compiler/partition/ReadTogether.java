package souther.compiler.partition;

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
     * What the ways a run takes read together.
     *
     * @param combinations the combinations some way reads, each written once with its positions in
     *                     the order the way met them
     * @param everyOneWith the positions every combination of which is read whatever the ways say
     */
    record Read(Set<Combination> combinations, Set<AxisId> everyOneWith) implements ReadTogether {

        public Read {
            combinations = Set.copyOf(combinations);
            everyOneWith = Set.copyOf(everyOneWith);
        }
    }

    /**
     * A class of one position and a class of another.
     *
     * @param one        the first position
     * @param oneClass   its class
     * @param other      the second position
     * @param otherClass its class
     */
    record Combination(AxisId one, String oneClass, AxisId other, String otherClass) {}

    /** Whether some run reads class {@code oneClass} of {@code one} together with class
     *  {@code otherClass} of {@code other}, or the reading cannot say that none does. */
    default boolean reads(AxisId one, String oneClass, AxisId other, String otherClass) {
        return switch (this) {
            case Every _ -> true;
            case Read it -> it.everyOneWith().contains(one) || it.everyOneWith().contains(other)
                    || it.combinations().contains(new Combination(one, oneClass, other, otherClass))
                    || it.combinations().contains(
                            new Combination(other, otherClass, one, oneClass));
        };
    }
}
