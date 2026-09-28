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
 * on this; what needs a number is on {@link Count}, which is the case that has one. A reader that
 * steps to the next value or takes the middle of two is a reader that has already established it is
 * on a carrier whose values step or fill, and it holds a {@link Count} by then.
 *
 * <p><b>Two places are only ever compared on one carrier.</b> A threshold and the value a row holds
 * at the position it cuts are places on the same order by construction, and nothing in the algebra
 * brings two carriers' places together. Comparing across them is a mistake in this compiler rather
 * than anything a model can write, and it is said as one.
 */
public sealed interface Place extends Comparable<Place> permits Count, Text {

    /**
     * What makes two places one line: what they are, and not how they were written.
     *
     * <p>{@code 0.00} and {@code 0} are one line. Named by the way they were written they are two,
     * and then a position has two classes both holding zero — which is not a partition, and the
     * classifier that reads a row against it has no answer.
     *
     * <p>A name and not a number to read: it is built from the parts of the canonical value, so
     * it costs what those parts cost and no reader should expect digits in it.
     */
    String key();

    /**
     * This place's coordinate written out as text: the number for a count, the string itself for a
     * string.
     *
     * <p>Three questions are asked of a place and this answers one of them. {@link #key()} names
     * it, this writes the coordinate the algebra holds — a day count is the number of days — and
     * what the carrier over it would show an author, a date for that day count, is the carrier's
     * to say ({@code Carrier#written}).
     *
     * <p>The value and not how it was written to the model: {@code 0.00} and {@code 0} come back the
     * same, which is the rule {@link #canonical()} states. A count held at a wide scale is a value
     * the algebra carries as cheaply as any other, and writing it is a character per place, so this
     * is for the reader that asked for the digits and for nothing that only tells two places apart.
     */
    String spelled();

    /** Whether this is the same place on the order as {@code other}, which is {@link #key()}'s
     * question asked of two rather than of one. */
    default boolean sameAs(Place other) {
        return other != null && compareTo(other) == 0;
    }

    /**
     * This place in the one representation {@link #key()} names.
     *
     * <p>For a caller that has to compare places it cannot ask {@link #sameAs} — a value used as a
     * map key, or held inside a larger value that is. Two places of one line come back equal here,
     * so the derived equality of whatever holds them answers the question the order would.
     *
     * <p>Beside the two above rather than replacing them: a place keeps the representation it was
     * read with, so {@code 0.00m} stays {@code 0.00m} where it is held. This is the same place in
     * the one representation, and it is only ever what an identity is built from.
     */
    Place canonical();

    /** What a comparison across two carriers is, where one happens. Never reachable from a model:
     * the places the algebra compares are the places of one position. */
    static IllegalArgumentException notOneOrder(Place left, Place right) {
        return new IllegalArgumentException(
                "two carriers' places compared: " + left + " against " + right);
    }
}
