package souther.compiler.partition;

import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;
import souther.compiler.numeric.UnheldNumber;

import java.util.List;

/**
 * One run of a quantity's order, between two places the rules stop it at.
 *
 * <p>The set and nothing else. Where a run is, what it holds, and where it stops are one answer here;
 * how it is written for a reader is the run's provenance and belongs to whatever drew it
 * ({@link Band}), because the same set is two different sentences depending on which rule is being
 * explained.
 *
 * <p><b>Convex on purpose.</b> Everything that asks an order about a region asks about one of these,
 * and a region that is not convex is a {@link LevelRegion} of several. Which end of a region to look
 * in first is a choice with no mathematical answer — a rule that singles a value out leaves the run
 * under it and the run over it, and neither is the nearer — so it is a searching policy and is kept
 * away from anything that answers about the set.
 *
 * <p>Whether this holds any value at all is the quantity's answer and not this one. Nothing lies
 * between one and two on an order that counts by threes, and every third of a decimal does; both are
 * this same interval, and telling them apart is what a {@link LevelSpace} is asked.
 *
 * @param low  where it starts, or null where nothing stops it that way
 * @param high where it stops, on the same reading
 */
public record LevelInterval(Bound low, Bound high) {

    /** Every value the order has. */
    public static final LevelInterval EVERYTHING = new LevelInterval(null, null);

    /** The same run with its ends written the one way, for an identity to be built from. */
    public LevelInterval canonical() {
        return new LevelInterval(low == null ? null : low.canonical(),
                high == null ? null : high.canonical());
    }

    /** The one level, and nothing else. */
    public static LevelInterval point(Level at) {
        return new LevelInterval(Bound.at(at, true), Bound.at(at, true));
    }

    /** Whether a value of the quantity lies in this run. */
    public boolean contains(Level value) {
        return (low == null || low.admitsFromBelow(value))
                && (high == null || high.admitsFromAbove(value));
    }

    /**
     * Whether the two ends cross, which is a run written down with nothing between them.
     *
     * <p>About where it stops and not about what the quantity takes. A run whose ends cross holds
     * nothing on any order; a run whose ends do not cross holds nothing on some orders and something
     * on others, and that is {@link LevelSpace}'s to say. Answered here, an order that counts by
     * threes would have every run between two of its lines called empty on every other order too.
     */
    public boolean crossed() {
        if (low == null || high == null) {
            return false;
        }
        int order = low.at().compareTo(high.at());
        return order > 0 || (order == 0 && !(low.inclusive() && high.inclusive()));
    }

    /** Whether this run is one place of the order, which is what a run written against a single
     *  value comes to. Everything wider than that has room for values between its ends. */
    public boolean onePlace() {
        return low != null && high != null && low.at().compareTo(high.at()) == 0;
    }

    /**
     * The same run without one value of it, which is one run or two.
     *
     * <p>What a point away from a border asks for: the run, less the value against the line. Two
     * where the value is inside, one where it is at an end, and this run unchanged where it is
     * outside — worked out by cases at each caller, a run was handed back holding the one value that
     * will not do.
     */
    public List<LevelInterval> without(Level value) {
        if (value == null || !contains(value)) {
            return List.of(this);
        }
        Bound at = Bound.at(value, false);
        List<LevelInterval> left = new java.util.ArrayList<>(2);
        LevelInterval under = new LevelInterval(low, at);
        LevelInterval over = new LevelInterval(at, high);
        if (!under.crossed()) {
            left.add(under);
        }
        if (!over.crossed()) {
            left.add(over);
        }
        return List.copyOf(left);
    }

    /** The values both runs hold, or null where their ends cross. */
    public LevelInterval intersect(LevelInterval other) {
        LevelInterval both = new LevelInterval(
                Bound.lower(low, other.low), Bound.upper(high, other.high));
        return both.crossed() ? null : both;
    }

    /**
     * How many digits it takes to name a number between this run's two ends.
     *
     * <p>Worked out from the ends and never guessed: two lines are a definite distance apart — a
     * third and a third and a hundred-billionth are — and how many digits a number between them
     * needs is what that distance says. Tried at a fixed handful of scales instead, a run narrower
     * than the widest of them was reported as one nothing lies inside, which is a false answer
     * rather than a search that gave up.
     *
     * <p>Nothing beyond whole numbers where the run has an end nothing bounds, since there is no
     * distance to read.
     *
     * @return the count, or which way the exact arithmetic could not hold the distance between the
     *         two ends — see {@link CutPosition#digitsToTellApartFrom}
     */
    public ExactAnswer<Integer> digitsToLookIn() {
        return low == null || high == null ? ExactAnswer.held(0)
                : low.at().digitsToTellApartFrom(high.at());
    }

    /**
     * What {@link #toLookIn} came to: an envelope, or which way the exact arithmetic could not
     * round an end inward.
     *
     * <p>Told apart from an end nothing bounds, which stays an envelope with that end absent: a run
     * this could not read at all is never a run whose digits happened to reach every value, and a
     * reader of {@link #toLookIn} that ran the two together read "this compiler could not work out
     * where to look" as "there is nowhere to look" — sound for {@link LevelSpace.Lattice#witness},
     * which only ever needs a candidate, and not sound for {@link LevelSpace.Lattice#inspect},
     * whose bound this feeds directly and which an absent end there widens to the carrier's own
     * extent.
     */
    public sealed interface LookedIn {

        /** The envelope, an end of it absent exactly where nothing bounds the run there. */
        record InBounds(NumericDomain.Bounds envelope) implements LookedIn {
            public InBounds {
                if (envelope == null) {
                    throw new IllegalArgumentException("an envelope is the bounds it is");
                }
            }
        }

        /** A model's own decimals put an end far enough from an ordinary one in scale that the
         *  exact arithmetic could not round it inward. */
        record NotWorkedOut(UnheldNumber why) implements LookedIn {
            public NotWorkedOut {
                if (why == null) {
                    throw new IllegalArgumentException("a refusal says why");
                }
            }
        }
    }

    /**
     * A range of plain numbers that lies inside this run, for something that counts to look in.
     *
     * <p>An envelope and never the run itself: what is in the run is {@link #contains}, and this
     * only says where to look. Where an end is at a place the quantity stands at no value of, the
     * envelope is narrowed inward to a number of {@code digits} digits past it — two thirds is past
     * no whole number below one and is past sixty-six hundredths, so a run between two thirds of a
     * decimal is looked in at the digits it has values at rather than at none.
     *
     * <p>Which is why what comes back has to be put to {@link #contains} before it stands for
     * anything. The envelope is inside the run and is not the run, and an end the run does hold is
     * carried as the end it is.
     *
     * <p><b>For a coordinate's own order and no other.</b> Narrowing inward loses a level no
     * decimal is, and that is sound exactly where the levels are a carrier's values, which every
     * decimal is one of. An order whose own values are a third apart has levels this envelope
     * cannot name, and asking it this way answers that a run holding one holds nothing — so
     * {@link LevelSpace.Lattice} reads its runs at the exact places they stop at
     * ({@link CutPosition#exactly}) and comes here only to look for something to write down.
     */
    public LookedIn toLookIn(int digits) {
        EndSought lo = lookingFrom(low, Towards.ABOVE, digits);
        if (lo instanceof EndSought.NotWorkedOut not) {
            return new LookedIn.NotWorkedOut(not.why());
        }
        EndSought hi = lookingFrom(high, Towards.BELOW, digits);
        if (hi instanceof EndSought.NotWorkedOut not) {
            return new LookedIn.NotWorkedOut(not.why());
        }
        return new LookedIn.InBounds(new NumericDomain.Bounds(
                lo instanceof EndSought.At(Endpoint endpoint) ? endpoint : null,
                hi instanceof EndSought.At(Endpoint endpoint) ? endpoint : null));
    }

    /** What one end of {@link #toLookIn} came to: nothing bounds the run there, a place, or which
     *  way the exact arithmetic could not round one inward. */
    private sealed interface EndSought {
        record Unbounded() implements EndSought {}

        record At(Endpoint endpoint) implements EndSought {}

        record NotWorkedOut(UnheldNumber why) implements EndSought {}
    }

    private static EndSought lookingFrom(Bound bound, Towards into, int digits) {
        if (bound == null) {
            return new EndSought.Unbounded();
        }
        // The end itself where the quantity has a value there and an order counts to it, which is
        // the end the run was named by. Rounded to a number first, an end the run holds became one
        // it stops short of. The second half is asked and not assumed: the rule may write the whole
        // of the quantity and still cut it where no order has a value — a third is what `d < 1 / 3`
        // writes — and that is an end to narrow inward past, exactly as a line a multiple left
        // between two values is.
        Level itself = bound.at().asALevelOfTheQuantity();
        Place named = itself == null ? null : itself.asAPlaceOrNothing();
        if (named != null) {
            return new EndSought.At(new Endpoint(named, bound.inclusive()));
        }
        return switch (bound.at().justBeyond(into, digits)) {
            case CutPosition.JustBeyond.At(Place inside) ->
                    new EndSought.At(Endpoint.inclusive(inside));
            case CutPosition.JustBeyond.NoNumericPlace _ -> new EndSought.Unbounded();
            case CutPosition.JustBeyond.NotWorkedOut(UnheldNumber why) ->
                    new EndSought.NotWorkedOut(why);
        };
    }

    @Override
    public String toString() {
        return (low == null ? "(" : low.toString()) + ", "
                + (high == null ? ")" : high.at().spelled() + (high.inclusive() ? "]" : ")"));
    }
}
