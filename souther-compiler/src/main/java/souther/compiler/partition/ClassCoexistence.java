package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.Requirements;
import souther.compiler.numeric.Count;

import java.util.ArrayList;
import java.util.Collections;
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
 * <p>Made once for the positions of one behavior and asked of each combination of their classes.
 * What a row at each class requires and which count classes hold nothing from one up are facts
 * about one class, and which position counts a container another is inside is a fact about two
 * positions. Each is worked out the first time it is asked and kept, rather than once for every
 * combination or every pair it takes part in.
 */
public final class ClassCoexistence {

    private final List<Axis> axes;

    /** What a row at each class requires, by position and class, for the positions asked about. */
    private final List<List<Requirements>> requiring;

    /** Which classes leave the container their position counts nothing to hold, by position and
     *  class, for the positions asked about. */
    private final boolean[][] leaveNothingInside;

    /** Whether one position stands inside a container another counts, by the two. */
    private final Boolean[][] inside;

    private ClassCoexistence(List<Axis> axes) {
        this.axes = List.copyOf(axes);
        this.requiring = new ArrayList<>(Collections.nCopies(axes.size(), null));
        this.leaveNothingInside = new boolean[axes.size()][];
        this.inside = new Boolean[axes.size()][axes.size()];
    }

    /** The answers for the classes of {@code axes}, asked of them by their indices. */
    public static ClassCoexistence among(List<Axis> axes) {
        return new ClassCoexistence(axes);
    }

    /**
     * Whether a row sitting in the {@code here}th class of the {@code one}th position and the
     * {@code there}th class of the {@code other}th at once is still possible, as far as the model
     * says.
     *
     * <p>One way only, as {@link Requirements#compatibleWith} is. False is a proof that no value
     * sits in both. True is not a proof that one does: it says nothing ruled the pair out, and a
     * reader wanting a value has to build one. Where the arithmetic could not say whether a count
     * class holds a count from one up, the answer is true.
     */
    public boolean canHoldTogether(int one, int here, int other, int there) {
        return !leavesNoRoom(one, here, other, there)
                && requiring(one).get(here).compatibleWith(requiring(other).get(there));
    }

    /**
     * Whether one of the two classes leaves the container the other position stands inside
     * nothing to hold: the half of {@link #canHoldTogether} beside the requirements, for a reader
     * that merges those itself.
     */
    public boolean leavesNoRoom(int one, int here, int other, int there) {
        return (inside(other, one) && leavesNothingInside(one)[here])
                || (inside(one, other) && leavesNothingInside(other)[there]);
    }

    private List<Requirements> requiring(int at) {
        List<Requirements> known = requiring.get(at);
        if (known == null) {
            Axis axis = axes.get(at);
            known = axis.classes().stream().map(axis::requiring).toList();
            requiring.set(at, known);
        }
        return known;
    }

    private boolean inside(int standing, int counting) {
        Boolean known = inside[standing][counting];
        if (known == null) {
            known = standsInside(axes.get(standing), axes.get(counting));
            inside[standing][counting] = known;
        }
        return known;
    }

    private boolean[] leavesNothingInside(int at) {
        boolean[] known = leaveNothingInside[at];
        if (known == null) {
            Axis counting = axes.get(at);
            known = new boolean[counting.classes().size()];
            for (int c = 0; c < known.length; c++) {
                known[c] = leavesNothingInside(counting, c);
            }
            leaveNothingInside[at] = known;
        }
        return known;
    }

    /**
     * Whether {@code counting} is how many some container {@code standing} is inside holds
     * ({@link Axis#countsWhatItsPathHolds}).
     *
     * <p>The half of the answer that is about the two positions alone, and the whole of what a
     * reader building a row asks to know whether the row's container has something asked inside it.
     */
    public static boolean standsInside(Axis standing, Axis counting) {
        return counting.countsWhatItsPathHolds()
                && standing.path().containersHoldingIt().contains(counting.path());
    }

    /**
     * Whether a row in the {@code cls}th class of {@code counting} holds nothing in the container
     * it counts: whether the class admits none of the counts from one up.
     *
     * <p>The half of the answer that is about one class alone.
     */
    private static boolean leavesNothingInside(Axis counting, int cls) {
        return counting.countsWhatItsPathHolds()
                && admitsNoCountFromOne(counting.classes().get(cls).recognises());
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
