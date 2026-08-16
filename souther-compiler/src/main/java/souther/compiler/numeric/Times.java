package souther.compiler.numeric;

import java.time.LocalTime;
import java.time.format.DateTimeParseException;

/**
 * A time of day as an order can hold it.
 *
 * <p>One direction only, and that is the whole of what this is for. Counting seconds from midnight
 * is order-preserving, which is everything a rule about where a {@code Time} stops needs; writing a
 * count back as a time is what a line drawn at one would need, and no line is drawn at a
 * {@code Time} (spec §a-line-is-drawn-where-the-values-can-carry-one). So the way back is absent
 * rather than written and left unused — a conversion nothing calls is a conversion nothing keeps
 * right.
 *
 * <p>A {@code Time} is held to the second (spec §a-local-temporal-is-held-to-the-second), so the
 * counts are whole and the day runs from 0 to 86399.
 */
public final class Times {

    /** The first and last counts a time of day can be written as. */
    public static final Count MIN = Count.of(0);

    public static final Count MAX = Count.of(86_399);

    /** The second of the day {@code iso} counts to, or null where it is not a time this reads. */
    public static Count secondOf(String iso) {
        if (iso == null) {
            return null;
        }
        try {
            LocalTime at = LocalTime.parse(iso);
            // Held to the second, so a text carrying a fraction of one is no `Time` and is refused
            // where it is written. Read here as a value this does not count, rather than rounded
            // onto a second the model did not name.
            return at.getNano() == 0 ? Count.of(at.toSecondOfDay()) : null;
        } catch (DateTimeParseException _) {
            return null;
        }
    }

    private Times() {}
}
