package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;

/**
 * One value a row has to be written at: a boundary, and the rule that drew it.
 *
 * <p>Carries the axis by id rather than the axis itself, so that what an obligation is about can be
 * held in a query answer without dragging the classes and their classifiers along with it.
 *
 * <p>An obligation from an invariant is met by a row whose value is the boundary. One from a guard is
 * not: the comparison has to have produced a value as well, because a value can reach the input of a
 * behavior without reaching the comparison that cares about it. Which row did that is read off the
 * site the guard's origin carries, and every guard origin has one.
 *
 * <p>The place is the count and the carrier it is on. Everything that compares a row against this
 * compares counts, and everything that writes or prints it asks the carrier — so a report, a
 * generated row and the rule that drew the line cannot disagree about which value the line is at.
 */
public record BoundaryObligation(AxisId axis, OriginRef origin, BoundarySide side,
                                 Carrier carrier, Count at) {

    public enum BoundarySide {
        /** The largest value on the low side of the cut. */
        BELOW,
        /** The cut itself. */
        AT,
        /** The smallest value on the high side of the cut. */
        ABOVE
    }

    /** The boundary as a value, which is what a row carries and what a person reads. */
    public ObservedValue value() {
        return carrier.valueOf(at);
    }

    /** The boundary as an author would write it. */
    public String written() {
        return carrier.written(at);
    }
}
