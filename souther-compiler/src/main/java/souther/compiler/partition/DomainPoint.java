package souther.compiler.partition;

import souther.compiler.numeric.Towards;

/**
 * Which point of a border, as a place on the quantity's order rather than as what that place is.
 *
 * <p><b>The identity, where {@link PointRole} is the classification.</b> Domain testing names four
 * points and a border can have two of them in one role: a rule that names a value has the values
 * beside it on both sides in the class it keeps out, and a row at one says nothing about the other.
 * So the role tells those two apart nowhere, and a reader keyed on it counts fewer things than there
 * are. What tells them apart is where they are, which is this, and what each of them <em>is</em>
 * follows from the place together with the rule ({@link PointRole#of}).
 *
 * <p>Three places and no more, because a line has three: the value the rule wrote, the value beside
 * it on a side, and a row away from it in the run on a side. Which of them a border owes is the
 * line's own answer — an order leaves the values on one side of it in the class its own value is in,
 * so there is no point against the line over there — and a border holds itself to the set its rule
 * says it has.
 */
public sealed interface DomainPoint {

    /**
     * The value the rule wrote, which every line has one of.
     *
     * <p>Or the nearest value the quantity takes, where it takes no value at the line: what the
     * point is is a row against the line, and which value that is is asked of the order.
     */
    record AtTheLine() implements DomainPoint {}

    /**
     * The nearest value on one side of the line, where the values there are in another class than
     * the line's own value.
     *
     * <p>One of these per side that answers to that. An order has one — the side it is satisfied on
     * holds the line's own value or is held by it, so the value one step that way is no point
     * against the line and is a row away from it instead. A rule that names a value has two.
     *
     * @param side which way from the line, on the order the quantity's values sit on
     */
    record BesideTheLine(Towards side) implements DomainPoint {

        public BesideTheLine {
            if (side == null) {
                throw new IllegalArgumentException("a value beside the line is beside it one way");
            }
        }
    }

    /**
     * A row away from the line, in the run of values on one side of it.
     *
     * <p>One per side, always both. Which of them is inside the partition the border bounds is the
     * rule's answer and no part of which point this is: the run above {@code n > 10} and the run
     * above {@code n < 10} are the same values and opposite roles.
     *
     * @param side which way from the line the run lies
     */
    record InTheRegion(Towards side) implements DomainPoint {

        public InTheRegion {
            if (side == null) {
                throw new IllegalArgumentException("a run beside the line lies one way of it");
            }
        }
    }

    /**
     * Whether this is one of the places the border names a value for, as against a run of them.
     *
     * <p>Half of what the role is, and the half the place answers on its own. The other half is
     * whether the rule holds there, which the place cannot say.
     */
    default boolean againstTheLine() {
        return !(this instanceof InTheRegion);
    }

    /** Which way of the line this lies, or null for the value the rule wrote — which is on the line
     *  and so on neither side of it. */
    default Towards side() {
        return switch (this) {
            case AtTheLine _ -> null;
            case BesideTheLine beside -> beside.side();
            case InTheRegion in -> in.side();
        };
    }
}
