package souther.compiler.partition;


/**
 * One place a row has to be written at: a boundary, and the rule that drew it.
 *
 * <p>Where the line is is {@link BoundaryTarget}'s to say, and it has more than one shape — a count of
 * one position, or two positions holding the same count. Held apart from the rule and the side so that
 * a reader asking which rule is owed this row does not have to know which shape the line has.
 *
 * <p>An obligation from an invariant is met by a row whose value is the boundary. One from a guard is
 * not: the comparison has to have produced a value as well, because a value can reach the input of a
 * behavior without reaching the comparison that cares about it. Which row did that is read off the
 * site the guard's origin carries, and every guard origin has one.
 */
public record BoundaryObligation(BoundaryTarget target, OriginRef origin, BoundarySide side) {

    public enum BoundarySide {
        /** The largest value on the low side of the cut. */
        BELOW,
        /** The cut itself. */
        AT,
        /** The smallest value on the high side of the cut. */
        ABOVE
    }

    /**
     * Which of the two points around a border this one is, in the words domain testing gives them.
     *
     * <p>Not a second spelling of {@link BoundarySide}. That says where the value sits around the cut
     * and is what says how to read {@link BoundaryTarget#right()}; this says what a row written there
     * is for. Which one a side is turns on whether the border is closed or open, so the same
     * {@code AT} is the {@code ON} point of {@code <= 3000} and the {@code OFF} point of
     * {@code < 3000} — two facts, and a report that kept one of them could not print the other.
     */
    public enum PointRole {
        /** Inside the partition the border bounds, and closest to the border. */
        ON,
        /** Outside it, and closest to the border. */
        OFF
    }

    /** Which point this obligation asks for. */
    public PointRole pointRole() {
        return pointRole(origin, side);
    }

    /**
     * The same, of an origin and a side apart from an obligation.
     *
     * <p>One derivation and no other. What is printed for a person, what the JSON carries and what a
     * row offered at the value is called are three readings of this — worked out three times they
     * would agree until one of them was corrected.
     *
     * <p>{@code holdsAtTheValue} is the whole of the input beside the side: the cut is inside the
     * partition exactly where the rule is satisfied there, which is what tells {@code <=} from
     * {@code <}. Every origin carries it, an invariant's included — its end is read rather than
     * assumed inclusive, and the ends that reach a report are inclusive because a strict bound on a
     * continuous carrier is dropped further down and not because a bound is always closed.
     *
     * <p>Answered for {@code BELOW} and {@code ABOVE} under a bound as well, though
     * {@link #besideTheCut} owes no row there. What a value one step outside a bound would be is not
     * in doubt, and a side with no answer would be a case a reader has to handle for a value that
     * never arrives.
     */
    public static PointRole pointRole(OriginRef origin, BoundarySide side) {
        boolean holds = holdsAtTheValue(origin);
        boolean inside = side == BoundarySide.AT ? holds : !holds;
        return inside ? PointRole.ON : PointRole.OFF;
    }

    /** Whether the cut value itself satisfies the rule that drew the line. */
    private static boolean holdsAtTheValue(OriginRef origin) {
        return switch (origin) {
            case OriginRef.GuardOrigin g -> g.holdsAtTheValue();
            case OriginRef.EnsuresOrigin e -> e.holdsAtTheValue();
            case OriginRef.InvariantOrigin i -> i.holdsAtTheValue();
            case OriginRef.NarrowedOrigin n -> holdsAtTheValue(n.bound());
        };
    }

    /**
     * How a row at this boundary describes itself.
     *
     * <p>The generator writes these same words on the row it offers, so a row and a note about the
     * boundary it stands for name it the same way.
     */
    public String label() {
        return target.left() + " = " + target.right();
    }

    /**
     * The value beside the cut a row is owed as well, or nothing where the line has no other side.
     *
     * <p>The second of the two questions, and independent of the first. What decides it is whether
     * the values either side of the line are both writable: a guard and a clause leave a range on
     * each side, and a bound leaves nothing outside itself, so an invariant's edge is the only row
     * there is to write. A value a rule singles out has no neighbour either — the values either
     * side of it are one class, so a row over there is a row that class already has.
     *
     * <p>Which neighbour it is comes from where the cut value itself falls: {@code <= 3000} leaves
     * 3001 over the line and {@code < 3000} leaves 2999.
     *
     * <p>Asked of the origin here rather than answered by it. Which rule drew a line and which side
     * of the line a row is owed on are two questions, and only the first is the rule's — the second
     * is what this measure does with the answer, and reading it off the origin put the vocabulary
     * of boundaries inside the identity every other measure of a rule shares.
     */
    public static java.util.Optional<BoundarySide> besideTheCut(OriginRef origin) {
        return switch (origin) {
            case OriginRef.GuardOrigin g -> g.singles() ? java.util.Optional.empty()
                    : java.util.Optional.of(g.valueBelongsBelow()
                            ? BoundarySide.ABOVE : BoundarySide.BELOW);
            case OriginRef.EnsuresOrigin e -> e.singles() ? java.util.Optional.empty()
                    : java.util.Optional.of(e.valueBelongsBelow()
                            ? BoundarySide.ABOVE : BoundarySide.BELOW);
            case OriginRef.NarrowedOrigin n -> besideTheCut(n.bound());
            case OriginRef.InvariantOrigin _ -> java.util.Optional.empty();
        };
    }
}
