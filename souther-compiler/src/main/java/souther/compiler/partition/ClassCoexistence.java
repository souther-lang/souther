package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.TakenAs;

import java.util.List;

/**
 * Whether a class of one position and a class of another can hold in one value.
 *
 * <p>False only where the model says they cannot, and never where a search came up short. A value
 * nothing could build for a combination proves nothing about it, and the combination stays owed;
 * what this answers is that there is no such value to build.
 *
 * <p>Two facts of the model say so. A position under one case of a sum is there only where the
 * case is ({@link Requirements}), so a class of it and another case of the sum are in no one value.
 * And a position inside a container is there only where the container holds something, so a class
 * of it and a class of how many the container holds that admits no count from one up are in no one
 * value either: an empty list has no element to hold the field.
 *
 * <p>One answer for every reader of a pair space. How many combinations there are and which of them
 * are left are two readings of one space, and a combination one of them leaves out and the other
 * keeps is a row asked for that no count will ever take.
 *
 * <p>Made once for two positions and asked of each combination of their classes. Which of the two
 * counts a container the other is inside, what a row at each class requires, and which count classes
 * hold nothing from one up are facts about one position or one class, and asked again for every
 * combination they would be worked out as many times as the other position has classes.
 */
public final class ClassCoexistence {

    private final List<Requirements> requiringOne;
    private final List<Requirements> requiringOther;
    private final boolean[] oneLeavesNoRoom;
    private final boolean[] otherLeavesNoRoom;

    private ClassCoexistence(Axis one, Axis other) {
        this.requiringOne = one.classes().stream().map(one::requiring).toList();
        this.requiringOther = other.classes().stream().map(other::requiring).toList();
        this.oneLeavesNoRoom = noRoomLeftBy(one, other);
        this.otherLeavesNoRoom = noRoomLeftBy(other, one);
    }

    /** The answers for the classes of {@code one} against the classes of {@code other}. */
    public static ClassCoexistence between(Axis one, Axis other) {
        return new ClassCoexistence(one, other);
    }

    /**
     * Whether a row sitting in the {@code here}th class of the first position and the
     * {@code there}th class of the second at once is still possible, as far as the model says.
     *
     * <p>One way only, as {@link Requirements#compatibleWith} is. False is a proof that no value
     * sits in both. True is not a proof that one does: it says nothing ruled the pair out, and a
     * reader wanting a value has to build one. Where the arithmetic could not say whether a count
     * class holds a count from one up, the answer is true.
     *
     * @param here  an index into the first position's classes
     * @param there an index into the second position's classes
     */
    public boolean canHoldTogether(int here, int there) {
        return !oneLeavesNoRoom[here] && !otherLeavesNoRoom[there]
                && requiringOne.get(here).compatibleWith(requiringOther.get(there));
    }

    /**
     * For each class of {@code counting}, whether it leaves no room for {@code standing}: whether
     * {@code counting} is how many some container {@code standing} is inside holds, and the class
     * admits none of the counts that would put anything in it.
     *
     * <p>How many the container itself holds, as it stands. A count of something made from it is a
     * count of another value, and an empty one says nothing about whether the container is.
     */
    private static boolean[] noRoomLeftBy(Axis counting, Axis standing) {
        boolean[] out = new boolean[counting.classes().size()];
        if (!(counting.term() instanceof NumericTerm.TakenOf taken)
                || !(taken.takenAs() instanceof TakenAs.HowManyItHolds)
                || !taken.transformation().equals(ValueTransformation.NONE)
                || !standing.path().containersHoldingIt().contains(taken.position())) {
            return out;
        }
        for (int c = 0; c < out.length; c++) {
            out[c] = admitsNoCountFromOne(counting.classes().get(c).recognises());
        }
        return out;
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
