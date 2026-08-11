package souther.compiler.numeric;

/**
 * Where a value sits on its carrier's order.
 *
 * <p>Four of the five carriers count to a number — a date counts days, a date-time seconds, an
 * {@code Int} itself, an enumeration the place its case is declared at — and the algebra was written
 * for exactly that: one number per position, and arithmetic on it wherever a range had to give up a
 * value. A {@code String} is ordered and has no number to count to, which is why it was left out of
 * the measure entirely rather than measured as far as it goes.
 *
 * <p>So the order and the arithmetic are told apart here. Everything the interval algebra needs of a
 * position's values in order to divide them — comparing two, telling two apart, writing one down — is
 * on this; what needs a number is on {@link Count}, which is the only case that has one. A reader
 * that steps to the next value or takes the middle of two is a reader that has already established
 * it is on a carrier whose values step or fill, and it holds a {@link Count} by then.
 *
 * <p><b>Two places are only ever compared on one carrier.</b> A threshold and the value a row holds
 * at the position it cuts are places on the same order by construction, and nothing in the algebra
 * brings two carriers' places together. Comparing across them is a mistake in this compiler rather
 * than anything a model can write, and it is said as one.
 */
public sealed interface Place extends Comparable<Place> permits Count {

    /**
     * What makes two places one line: what they are, and not how they were written.
     *
     * <p>{@code 0.00} and {@code 0} are one line. Keyed by their own spelling they are two, and then
     * a position has two classes both holding zero — which is not a partition, and the classifier
     * that reads a row against it has no answer.
     */
    String key();

    /** Whether this is the same place on the order as {@code other}, which is {@link #key()}'s
     * question asked of two rather than of one. */
    default boolean sameAs(Place other) {
        return other != null && compareTo(other) == 0;
    }

    /** What a comparison across two carriers is, where one happens. Never reachable from a model:
     * the places the algebra compares are the places of one position. */
    static IllegalArgumentException notOneOrder(Place left, Place right) {
        return new IllegalArgumentException(
                "two carriers' places compared: " + left + " against " + right);
    }
}
