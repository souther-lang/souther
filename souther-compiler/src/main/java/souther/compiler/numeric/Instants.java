package souther.compiler.numeric;

import java.math.BigDecimal;
import java.time.Instant;
import java.time.format.DateTimeParseException;

/**
 * A moment on the timeline as an order can hold it.
 *
 * <p>One direction only, for the reason {@link Times} is: counting is what a rule about where an
 * {@code Instant} stops needs, and writing a count back is what a line drawn at one would need. No
 * line is drawn at an {@code Instant} (spec §a-line-is-drawn-where-the-values-can-carry-one).
 *
 * <p><b>Nanoseconds, and this is why it is not the date-time's carrier.</b> An {@code Instant} is
 * held to the nanosecond (spec §an-instant-carries-what-a-timestamp-said) where a {@code DateTime}
 * is held to the second, so the two count in different units and a count of one is not a count of
 * the other. The numbers run past what a {@code long} holds, which is no trouble here: a place is a
 * {@link Count} and a count is a {@code BigDecimal}.
 */
public final class Instants {

    private static final BigDecimal PER_SECOND = BigDecimal.valueOf(1_000_000_000L);

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

    private Instants() {}
}
