package souther.compiler.partition;

import souther.compiler.numeric.Towards;

/**
 * What a quantity has in one run of its order.
 *
 * <p><b>One answer rather than two, because the two were read as one.</b> Whether a run holds
 * anything and whether it has a first value are different facts, and an order whose values fill
 * answers yes to the first and no to the second: every third of a decimal lies between one and two,
 * and there is no least one. Handed back as an empty {@code Optional} the two are the same shape,
 * and every reader that had a first value to reach for read "none" as "nothing there" — which is the
 * mistake this compiler made about the side of a border, about the value beside a line, and about a
 * run bounded at both ends, once each (issues #880, #901, #903).
 *
 * <p>Apart from {@link Witness}, which is the other question: whether this compiler can write a
 * value of the run down. The two are independent, and all four of their combinations mean something
 * — a run of strings above a bound is inhabited and has nothing this will name, because naming one
 * means choosing a character the model never wrote.
 */
public sealed interface Occupancy {

    /** The quantity takes no value at all in this run. */
    record Empty() implements Occupancy {}

    /**
     * It takes at least one.
     *
     * @param least    the first value in the run, or null where it has none — which is not a run
     *                 with nothing in it, but one whose values fill up to its lower end
     * @param greatest the last, on the same reading
     */
    record Inhabited(Level least, Level greatest) implements Occupancy {}

    /** Whether the quantity takes any value here, which is what this exists to be asked. */
    default boolean any() {
        return this instanceof Inhabited;
    }

    /** The value at one end of the run, where the run has one there. */
    default Level end(Towards towards) {
        if (!(this instanceof Inhabited in)) {
            return null;
        }
        return towards == Towards.ABOVE ? in.least() : in.greatest();
    }
}
