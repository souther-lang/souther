package souther.compiler.numeric;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.Instant;
import java.time.format.DateTimeParseException;

/**
 * A moment on the timeline as an order can hold it.
 *
 * <p>Both directions, for the reason {@link Times} has both: counting is what a rule about where an
 * {@code Instant} stops needs, and writing a count back is what a line drawn at one needs (spec
 * §a-line-is-drawn-where-the-values-can-carry-one).
 *
 * <p><b>Nanoseconds, and this is why it is not the date-time's carrier.</b> An {@code Instant} is
 * held to the nanosecond (spec §an-instant-carries-what-a-timestamp-said) where a {@code DateTime}
 * is held to the second, so the two count in different units and a count of one is not a count of
 * the other. The numbers run past what a {@code long} holds, which is no trouble here: a place is a
 * {@link Count} and a count is a {@code BigDecimal}.
 */
public final class Instants {

    private static final BigDecimal PER_SECOND = BigDecimal.valueOf(1_000_000_000L);
    private static final BigInteger PER_SECOND_NANOS = BigInteger.valueOf(1_000_000_000L);

    /** The first and last counts a moment can be written as. */
    public static final Count MIN = countAt(Instant.MIN);

    public static final Count MAX = countAt(Instant.MAX);

    private static Count countAt(Instant at) {
        return Count.of(BigDecimal.valueOf(at.getEpochSecond()).multiply(PER_SECOND)
                .add(BigDecimal.valueOf(at.getNano())));
    }

    /** The nanosecond {@code iso} counts to, or null where it is not a moment this reads. */
    public static Count nanoOf(String iso) {
        if (iso == null) {
            return null;
        }
        try {
            return countAt(Instant.parse(iso));
        } catch (DateTimeParseException _) {
            return null;
        }
    }

    /**
     * The moment {@code count} counts to, written the way a model writes one.
     *
     * <p>Split rather than handed over whole because the count runs past what a {@code long} holds
     * at either end of the timeline, and {@code ofEpochSecond} takes two of them. Which way the
     * division goes does not matter: below the epoch it leaves a negative count of nanoseconds
     * within the second, and {@code ofEpochSecond} normalises that onto the second before — the
     * same moment a division towards the count below would have named.
     *
     * @throws IllegalStateException where the exact arithmetic could not hold the floor of
     *         {@code count}, the same as {@link DateTimes#written} throws for its own count
     */
    public static String written(Place count) {
        if (!(Count.number(count).exactly().floor()
                instanceof ExactAnswer.Held<BigInteger> held)) {
            throw new IllegalStateException(
                    "a count read or written as a moment is one the exact arithmetic can hold the"
                            + " floor of, and this was not: " + count);
        }
        BigInteger[] parts = held.value().divideAndRemainder(PER_SECOND_NANOS);
        return Instant.ofEpochSecond(parts[0].longValueExact(), parts[1].longValueExact())
                .toString();
    }

    private Instants() {}
}
