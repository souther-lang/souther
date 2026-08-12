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
     * How a row at this boundary describes itself.
     *
     * <p>The generator writes these same words on the row it offers, so a row and a note about the
     * boundary it stands for name it the same way.
     */
    public String label() {
        return target.left() + " = " + target.right();
    }
}
