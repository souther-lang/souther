package souther.compiler.partition;

import souther.compiler.observe.ObservedValue;

/**
 * One value a row has to be written at: a boundary, and the rule that drew it.
 *
 * <p>Carries the axis by id rather than the axis itself, so that what an obligation is about can be
 * held in a query answer without dragging the classes and their classifiers along with it.
 *
 * <p>An obligation from an invariant is met by a row whose value is the boundary. One from a guard is
 * not: the guard has to have been evaluated as well, because a value can reach the input of a
 * behavior without reaching the comparison that cares about it.
 */
public record BoundaryObligation(AxisId axis, OriginRef origin, BoundarySide side,
                                 ObservedValue value) {

    public enum BoundarySide {
        /** The largest value on the low side of the cut. */
        BELOW,
        /** The cut itself. */
        AT,
        /** The smallest value on the high side of the cut. */
        ABOVE
    }
}
