package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.TakenAs;

/**
 * Whether a class of one position and a class of another can hold in one value.
 *
 * <p>False only where the model says they cannot, and never where a search came up short. A value
 * nothing could build for a combination proves nothing about it, and the combination stays owed;
 * what this answers is that there is no such value to build.
 *
 * <p>Two facts of the model say so. A position under one case of a sum is there only where the
 * case is ({@link souther.compiler.inputs.Requirements}), so a class of it and another case of the
 * sum are in no one value. And a position inside a container is there only where the container holds
 * something, so a class of it and a class of how many the container holds that admits no count from
 * one up are in no one value either: an empty list has no element to hold the field.
 *
 * <p>One answer for every reader of a pair space. How many combinations there are and which of them
 * are left are two readings of one space, and a combination one of them leaves out and the other
 * keeps is a row asked for that no count will ever take.
 */
public final class ClassCoexistence {

    private ClassCoexistence() {
    }

    /**
     * Whether a row sitting in {@code here} at {@code one} and in {@code there} at {@code other} at
     * once is still possible, as far as the model says.
     *
     * <p>One way only, as {@link souther.compiler.inputs.Requirements#compatibleWith} is. False is a
     * proof that no value sits in both. True is not a proof that one does: it says nothing ruled the
     * pair out, and a reader wanting a value has to build one. Where the arithmetic could not say
     * whether a count class holds a count from one up, the answer is true.
     */
    public static boolean canHoldTogether(Axis one, PartitionClass here,
                                          Axis other, PartitionClass there) {
        return one.requiring(here).compatibleWith(other.requiring(there))
                && !leavesNoRoomFor(one, here, other)
                && !leavesNoRoomFor(other, there, one);
    }

    /**
     * Whether {@code counting} is how many some container {@code standing} is inside holds, and
     * {@code cls} admits none of the counts that would put anything in it.
     *
     * <p>How many the container itself holds, as it stands. A count of something made from it is a
     * count of another value, and an empty one says nothing about whether the container is.
     */
    private static boolean leavesNoRoomFor(Axis counting, PartitionClass cls, Axis standing) {
        return counting.term() instanceof NumericTerm.TakenOf taken
                && taken.takenAs() instanceof TakenAs.HowManyItHolds
                && taken.transformation().equals(ValueTransformation.NONE)
                && standing.path().containersHoldingIt().contains(taken.position())
                && admitsNoCountFromOne(cls.recognises());
    }

    /**
     * Whether a class of a count holds no count of one or more.
     *
     * <p>Asked of the set the class is about, run by run, and true only where every run is shown to
     * hold nothing there. A run the order could not read is not one shown empty, so the class is
     * kept rather than taken out on a guess.
     */
    private static boolean admitsNoCountFromOne(Recognition what) {
        return switch (what) {
            case Recognition.OfACount count -> holdsNothingFromOne(count.is(), count.carrier());
            case Recognition.Under under -> admitsNoCountFromOne(under.inner());
            case Recognition.Truth _, Recognition.Held _, Recognition.AtAValue _,
                 Recognition.OfASet _, Recognition.OfCase _, Recognition.Nothing _ -> false;
        };
    }

    private static boolean holdsNothingFromOne(NumericSet counts, Carrier carrier) {
        LevelRegion fromOne = counts.region(carrier).meet(LevelRegion.of(new LevelInterval(
                Bound.at(new Level.OnACarrier(carrier, Count.of(1)), true), null)));
        LevelSpace space = LevelSpace.onACarrier(carrier);
        for (LevelInterval part : fromOne.parts()) {
            if (!(space.inspect(part) instanceof Occupancy.Empty)) {
                return false;
            }
        }
        return true;
    }
}
