package souther.compiler.partition;

import souther.compiler.check.OriginRef;

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
     * of boundaries inside the identity every other measure of a rule shares (issue #852).
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
