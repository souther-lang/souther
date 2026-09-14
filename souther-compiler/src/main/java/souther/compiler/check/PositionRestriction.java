package souther.compiler.check;

import souther.compiler.numeric.OrderedInterval;

/**
 * Where one position must sit, as far as the readings outside the one being asked can say.
 *
 * <p>A necessary condition and never the whole of what a reading holds. What is met here is one
 * position at a time, so a rule relating two of them arrives as whatever each of them cannot help
 * lying between: {@code x == y} with neither end written leaves both at {@link Within} with an open
 * interval, which is true and is less than the rule says. Nothing about a pair survives the meeting,
 * and a reader wanting that is asking a question this cannot be the answer to.
 *
 * <p><b>Saying nothing and placing no edge are two answers.</b> Both leave a position where it was,
 * and they are told apart because a reader composing several of these has to know which readings
 * spoke: a position no reading outside this one mentions is one whose account is its own, and a
 * position spoken about and left open is one whose rules were read to the end. Held as one, the
 * distinction is gone at the first reading that has to write down why a position is as wide as it
 * is.
 */
sealed interface PositionRestriction {

    /** Nothing outside the reading being asked says anything about the position. */
    record NotSpokenOf() implements PositionRestriction {}

    /** The rules outside it prove the position lies in {@code interval}, which is every value
     *  wherever they place no edge. */
    record Within(OrderedInterval interval) implements PositionRestriction {}

    /** The interval this restricts a position to, which is every value where it restricts none. */
    default OrderedInterval interval() {
        return this instanceof Within it ? it.interval() : OrderedInterval.OPEN;
    }

    /** Whether this leaves the position anywhere it could have been without it. */
    default boolean saysNothing() {
        return !(this instanceof Within it) || it.interval().equals(OrderedInterval.OPEN);
    }
}
