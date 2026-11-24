package souther.compiler.numeric;

/**
 * Where a number no rule fixes is looked for first, or that it has no such place.
 *
 * <p>A date is near today, and so is its year; a whole number, a decimal, a time of day, a case
 * and a string have nowhere they are usually near, and a range of them is entered from its end.
 * Said by every reader that chooses a value — none of them is left to assume an answer — so a
 * reader added later says which it means rather than inheriting the end of the order.
 */
public sealed interface UsualPlace {

    /** A number with no usual place: a range of it is entered from its end. */
    UsualPlace NONE = new None();

    /**
     * Near {@code at}, on an order that runs from {@code least} to {@code greatest} of its own.
     *
     * <p>The ends are what tell a side of a range a rule drew from one it was left: an end at or
     * past the order's own bounds nothing, and a range entered from such a side is entered nearest
     * {@link #at}.
     *
     * @param at       the place itself, as the day today is of a date
     * @param least    the least value the order has
     * @param greatest the greatest value the order has
     */
    record Near(Place at, Place least, Place greatest) implements UsualPlace {

        public Near {
            if (at == null || least == null || greatest == null) {
                throw new IllegalArgumentException("a usual place is a place between two ends");
            }
        }

        /** Whether {@code end}, a lower end where {@code lower}, bounds nothing a rule drew: there
         *  is none, or it is at or past the order's own. */
        public boolean leftOpenAt(Endpoint end, boolean lower) {
            return end == null || (lower ? end.at().compareTo(least) <= 0
                    : end.at().compareTo(greatest) >= 0);
        }

        /** Whether a range from {@code low} to {@code high} is left open on either side. */
        public boolean leftOpenIn(Endpoint low, Endpoint high) {
            return leftOpenAt(low, true) || leftOpenAt(high, false);
        }
    }

    /** No usual place. */
    record None() implements UsualPlace {}
}
