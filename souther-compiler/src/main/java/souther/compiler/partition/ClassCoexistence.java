package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

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
 * <p>A third, where the declarations are handed in: a rule between two numbers leaves what one is
 * at no room where the other is, and {@code a < b} leaves no {@code b} under 500 for an {@code a}
 * from 1000. Taken in as where each class lies ({@link NumericSet#extent}) over the region the
 * declarations leave, the two are in no one value where that region is shown empty. The extent
 * holds every number of the class and may hold more, which only keeps a combination that could be
 * ruled out; the region is no narrower than the values the declarations leave, so emptiness is a
 * proof and anything short of it is not.
 *
 * <p>One answer for every reader of the classes of two positions: the combinations a pair space owes
 * are listed once with it, and how many there are and which are left are read off that list, so a
 * combination this rules out is neither counted nor asked a row for.
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

    /** What the declarations leave, or null where the numbers of the classes are not asked of
     *  them. */
    private final SearchRegion declared;

    /** The declared region with the extent of each class taken in, by position and class. */
    private final SearchRegion[][] regions;

    /** Whether a rule relates the numbers of two positions, by the two. */
    private final Boolean[][] related;

    private ClassCoexistence(List<Axis> axes, SearchRegion declared) {
        this.axes = List.copyOf(axes);
        this.declared = declared;
        this.requiring = new ArrayList<>(Collections.nCopies(axes.size(), null));
        this.leaveNothingInside = new boolean[axes.size()][];
        this.inside = new Boolean[axes.size()][axes.size()];
        this.regions = new SearchRegion[axes.size()][];
        this.related = new Boolean[axes.size()][axes.size()];
    }

    /**
     * The answers for the classes of {@code axes}, asked of them by their indices, where the
     * numbers of the classes are not asked of any rule.
     */
    public static ClassCoexistence among(List<Axis> axes) {
        return new ClassCoexistence(axes, null);
    }

    /**
     * The answers for the classes of {@code axes}, where the rules between their numbers are those
     * of {@code declared}: the region the declarations leave and nothing a way narrowed, since a
     * combination the way leaves out is still one a row is owed.
     */
    public static ClassCoexistence among(List<Axis> axes, SearchRegion declared) {
        return new ClassCoexistence(axes, declared);
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
                && requiring(one).get(here).compatibleWith(requiring(other).get(there))
                && !theNumbersLeaveNoRoom(one, here, other, there);
    }

    /**
     * Whether the declarations leave no value with the number of the one position in its class
     * and the number of the other in its.
     *
     * <p>Asked only of two positions a rule relates: numbers no rule relates are free of one
     * another, and no class of one rules out a class of the other.
     */
    private boolean theNumbersLeaveNoRoom(int one, int here, int other, int there) {
        if (declared == null || !relates(one, other)) {
            return false;
        }
        SearchRegion both = within(heldToEachClass(one)[here], axes.get(other),
                axes.get(other).classes().get(there));
        return both.emptiness().isPresent();
    }

    private boolean relates(int one, int other) {
        Boolean known = related[one][other];
        if (known == null) {
            known = declared.relates(Set.of(axes.get(one).term()), Set.of(axes.get(other).term()));
            related[one][other] = known;
        }
        return known;
    }

    /** The declared region held to each class of the position, by class. */
    private SearchRegion[] heldToEachClass(int at) {
        SearchRegion[] known = regions[at];
        if (known == null) {
            Axis axis = axes.get(at);
            known = axis.classes().stream().map(each -> within(declared, axis, each))
                    .toArray(SearchRegion[]::new);
            regions[at] = known;
        }
        return known;
    }

    /**
     * {@code region} with the extent of {@code cls} taken in as where the number of {@code axis}
     * lies, or as it was where the class is about no number or an end is not one the region
     * orders.
     */
    private static SearchRegion within(SearchRegion region, Axis axis, PartitionClass cls) {
        NumericSet numbers = cls.recognises().numbers();
        if (numbers == null) {
            return region;
        }
        NumericDomain.Bounds extent = numbers.extent();
        SearchRegion held = region;
        if (extent.min() != null) {
            held = held(held, axis.term(), extent.min(),
                    extent.min().inclusive() ? Rel.GE : Rel.GT);
        }
        if (extent.max() != null) {
            held = held(held, axis.term(), extent.max(),
                    extent.max().inclusive() ? Rel.LE : Rel.LT);
        }
        return held;
    }

    /** {@code region} with {@code term rel end} taken in, as it was where the region cannot carry
     *  it. */
    private static SearchRegion held(SearchRegion region, NumericTerm.FromOnePosition term,
                                     Endpoint end, Rel rel) {
        if (!(end.at() instanceof Count count)) {
            return region.assuming(term, end.at(), rel);
        }
        return region.assuming(LinearForm.atomMinusConstant(term, count.exactly()), rel)
                instanceof SearchRegion.Assumption.Taken(SearchRegion taken) ? taken : region;
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
        return switch (counts) {
            // Progressions say it of their members: none from one is none at or above one.
            case NumericSet.InTheNumbers members ->
                    members.numbers().leastAtOrAbove(BigInteger.ONE) == null;
            case NumericSet.OfRuns runs -> holdsNothingFromOne(runs, carrier);
        };
    }

    private static boolean holdsNothingFromOne(NumericSet.OfRuns counts, Carrier carrier) {
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
