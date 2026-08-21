package souther.compiler.numeric;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * Everything a set of rules is worked out to leave, derived once and read by every question.
 *
 * <p>One derivation and one answer. What a position is left, whether one sum follows from another,
 * whether anything is left at all — these had been answered by readings that could disagree, and one
 * of them did: a projection said a position ran to sixteen while the proof it was read beside could
 * not show it. Both were sound and they were not the same abstract state, which is a thing to fix
 * rather than a thing to live with.
 *
 * <p>Derived from the canonical rules and nothing else. Not from the order they arrived in, not from
 * what was written into a bound at the moment a rule was read. Two runs given the same rules produce
 * the same state, whatever order they were handed over in and however many times each was said.
 *
 * <p><b>Two things closed against each other.</b> The rules of difference-bound shape are closed
 * exactly ({@link DifferenceBounds}). The rest — a sum over several positions, weighted unevenly —
 * are read the other way against what the closure leaves ({@link AffineReduction}), and what that
 * finds goes back through the differences, and round again. A round reads only what the round before
 * it produced, so no rule's answer depends on which rule ran first.
 *
 * <p><b>The rounds are not run to a fixed point, and do not claim to be.</b> Narrowing over a general
 * sum need not settle in finitely many rounds: two rules each halving the other's bound descend
 * forever without arriving. So the rounds are bounded, and where the bound is reached the state says
 * {@link Status#BUDGET_EXHAUSTED} — meaning the box is sound but the rules were not read against it
 * until it stopped moving. Stopping early only ever leaves it wider, so nothing this claims rests on
 * the bound.
 *
 * <p><b>The box itself is a fixed point of the differences, whichever way the rounds left.</b> Each
 * round carries the box along them before the next one reads it, so what is handed back is a box no
 * relation can still narrow — and that, rather than the rounds having settled, is what a reading of
 * one position at a time rests on. Asserted where the state is made and held to as a property
 * elsewhere.
 *
 * <p><b>What emptiness means here, in one direction.</b> Where this says nothing is left, nothing is
 * — every step that narrows is implied by the rules, so a box that has closed on itself is a proof.
 * The other way round does not hold: the rounds can stop early, and a general sum is reasoned about
 * approximately, so a state that has not shown emptiness is not a state with a value in it.
 */
public final class ClosedState<A> {

    /**
     * How many rounds of reading the general rules against the box are worth running.
     *
     * <p>A number and not a proof of one. Every round is sound and every round only narrows, so
     * stopping is always safe and never wrong — what a larger number buys is precision on the rules
     * that need several passes to say what they say, and what it costs is time on the ones that
     * settled in the first round and would have settled anyway.
     */
    static final int ROUNDS = 16;

    /** Whether the rounds ran out before the box stopped moving. */
    public enum Status {

        /** The box closed on itself: another round would find nothing further. */
        STABLE,

        /**
         * The rounds ran out with the box still moving.
         *
         * <p>About the derivation and never a thing to branch on. The box is sound either way, and a
         * reader that behaved differently here would behave differently on rules that happen to take
         * one round longer than some other rules — which is not a distinction the language makes.
         *
         * <p>Not a hypothesis of anything either, and in particular not of whether the ranges can be
         * certified as the whole of what the rules leave. What that needs is the box being a fixed
         * point of the differences, which holds here as well — see the class comment. Asking for the
         * rounds to have settled on top of it would be a condition the theorem does not have, buying
         * no soundness and refusing certificates that hold.
         */
        BUDGET_EXHAUSTED
    }

    private final Box<A> box;
    private final DifferenceBounds<A> differences;
    private final boolean holdsNothing;
    private final Status status;

    private ClosedState(Box<A> box, DifferenceBounds<A> differences, boolean holdsNothing,
                        Status status) {
        this.box = box;
        this.differences = differences;
        this.holdsNothing = holdsNothing;
        this.status = status;
    }

    /** What {@code constraints} leave, worked out. */
    public static <A> ClosedState<A> of(List<AffineConstraint<A>> constraints,
                                        Function<A, Granularity> spacing) {
        DifferenceBounds<A> differences = DifferenceBounds.over(constraints);
        if (differences.holdsNothing()) {
            return empty(differences);
        }
        Set<A> positions = positionsOf(constraints);
        Box<A> box = boxOf(differences, positions);
        if (!box.holdsAValue()) {
            return empty(differences);
        }
        for (int round = 0; round < ROUNDS; round++) {
            AffineReduction.Reduction<A> found =
                    AffineReduction.over(constraints, box, spacing);
            if (found instanceof AffineReduction.Reduction.NothingIsLeft) {
                return empty(differences);
            }
            AffineReduction.Reduction.Tightened<A> tightened =
                    (AffineReduction.Reduction.Tightened<A>) found;
            Box<A> next = throughDifferences(
                    box.meeting(tightened.atLeast(), tightened.atMost()), differences, positions);
            if (!next.holdsAValue()) {
                return empty(differences);
            }
            if (next.equals(box)) {
                return settled(box, differences, Status.STABLE);
            }
            box = next;
        }
        return settled(box, differences, Status.BUDGET_EXHAUSTED);
    }

    /**
     * A state with a box no difference can still narrow, which is what every reading of a range
     * rests on.
     *
     * <p>Asserted at the one place a state with a box is made. The rounds carry the box along the
     * differences at the end of each of them, so this holds however the loop left — and a reader
     * taking a range as the whole of what the rules leave a position is depending on it whether or
     * not the rounds settled.
     */
    /**
     * The box carried along the differences, over the positions it has bounds for.
     *
     * <p>One expression rather than two. The check that a box about to be handed back is a fixed
     * point and the answer a reader asks for are the same carry, and a second spelling of it is a
     * second chance to disagree about which positions it is over — where they disagreed, one of them
     * would be checking a property the other does not have.
     */
    private static <A> Box<A> carriedAlong(Box<A> box, DifferenceBounds<A> differences) {
        return throughDifferences(box, differences, box.positions());
    }

    private static <A> ClosedState<A> settled(Box<A> box, DifferenceBounds<A> differences,
                                              Status status) {
        assert box.equals(carriedAlong(box, differences))
                : "a difference still narrows the box that is about to be handed back";
        return new ClosedState<>(box, differences, false, status);
    }

    private static <A> ClosedState<A> empty(DifferenceBounds<A> differences) {
        return new ClosedState<>(Box.unbounded(), differences, true, Status.STABLE);
    }

    private static <A> Set<A> positionsOf(List<AffineConstraint<A>> constraints) {
        Set<A> out = new LinkedHashSet<>();
        constraints.forEach(each -> out.addAll(each.form().coefs().keySet()));
        return out;
    }

    /** What the closed differences leave each position on its own. */
    private static <A> Box<A> boxOf(DifferenceBounds<A> differences, Set<A> positions) {
        Map<A, RationalCut> least = new LinkedHashMap<>();
        Map<A, RationalCut> most = new LinkedHashMap<>();
        for (A position : positions) {
            RationalCut low = differences.lowerBoundOf(position);
            if (low != null) {
                least.put(position, low);
            }
            RationalCut high = differences.upperBoundOf(position);
            if (high != null) {
                most.put(position, high);
            }
        }
        return new Box<>(least, most);
    }

    /**
     * The box carried along the differences: what one position is left bounds every position held
     * against it.
     *
     * <p>Run after each round rather than once at the start. A bound the general rules found on one
     * position is a bound on every position a difference relates it to, and a reading that closed the
     * differences only at the start would answer differently depending on whether a rule happened to
     * arrive as a difference or as a sum — which is the spelling deciding the answer again, one level
     * up.
     */
    private static <A> Box<A> throughDifferences(Box<A> box, DifferenceBounds<A> differences,
                                                 Set<A> positions) {
        Map<A, RationalCut> least = new LinkedHashMap<>();
        Map<A, RationalCut> most = new LinkedHashMap<>();
        for (A here : positions) {
            RationalCut high = box.mostOf(here);
            RationalCut low = box.leastOf(here);
            for (A there : positions) {
                if (here.equals(there)) {
                    continue;
                }
                // `here - there <= d` with `there <= h` puts `here` at `h + d`.
                RationalCut apart = differences.differenceBound(here, there);
                if (apart != null && box.mostOf(there) != null) {
                    high = RationalCut.tighterUpper(high,
                            RationalCut.meetingBoth(box.mostOf(there), apart));
                }
                // `there - here <= d` with `there >= l` puts `here` at `l - d`.
                RationalCut back = differences.differenceBound(there, here);
                if (back != null && box.leastOf(there) != null) {
                    low = RationalCut.tighterLower(low, new RationalCut(
                            box.leastOf(there).at().minus(back.at()),
                            box.leastOf(there).inclusive() && back.inclusive()));
                }
            }
            if (low != null) {
                least.put(here, low);
            }
            if (high != null) {
                most.put(here, high);
            }
        }
        return new Box<>(least, most);
    }

    /**
     * Whether nothing at all satisfies the rules together.
     *
     * <p>True is a proof and false is not. See the class comment: every narrowing is implied, so a
     * box that has emptied is a box the rules emptied — but the rounds can stop early and a general
     * sum is read approximately, so nothing here is entitled to conclude that a value exists.
     */
    public boolean holdsNothing() {
        return holdsNothing;
    }

    /**
     * What each position is left.
     *
     * @throws IllegalStateException where nothing is left, for the reason
     *         {@link DifferenceBounds} refuses it there: no bound is the tightest when every bound
     *         holds, and "no bound" reads as unbounded, which is the opposite of the truth
     */
    public Box<A> box() {
        if (holdsNothing) {
            throw new IllegalStateException(
                    "nothing is left, so there is no box; ask holdsNothing first");
        }
        return box;
    }

    /** The difference-bound part, closed, for a question about two positions rather than one. */
    public DifferenceBounds<A> differences() {
        return differences;
    }

    /**
     * The box carried along the differences once more, which is the box it already was.
     *
     * <p>Here so that the property every reading of a range rests on can be checked rather than
     * argued for. What makes a range the whole of what the rules leave a position is that no
     * difference can carry another position's end onto it and find it loose, and that is this being
     * a fixed point.
     */
    Box<A> boxCarriedAlongTheDifferences() {
        return carriedAlong(box(), differences);
    }

    /** Whether the rounds settled. Metadata about the derivation; see {@link Status}. */
    Status status() {
        return status;
    }
}
