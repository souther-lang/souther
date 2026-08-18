package souther.compiler.numeric;

import java.math.RoundingMode;
import java.time.LocalTime;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;

/**
 * A time of day as an order can hold it.
 *
 * <p>Both directions. Counting seconds from midnight is order-preserving, which is what a rule
 * about where a {@code Time} stops needs; writing a count back as a time is what a line drawn at
 * one needs, and lines are drawn at a {@code Time} (spec
 * §a-line-is-drawn-where-the-values-can-carry-one). The way back was left out while nothing called
 * it, and what that cost was the line: a {@code guard} comparing an input against a written time
 * came back saying no line could be drawn on values the language orders.
 *
 * <p>A {@code Time} is held to the second (spec §a-local-temporal-is-held-to-the-second), so the
 * counts are whole and the day runs from 0 to 86399.
 */
public final class Times {

    /** The first and last counts a time of day can be written as. */
    public static final Count MIN = Count.of(0);

    public static final Count MAX = Count.of(86_399);

    /** Seconds are spelled out even at zero, so the text a boundary is named by is the text a model
     * writes. {@code LocalTime.toString} drops them, and a line at four o'clock would then be
     * printed one way and written another. */
    private static final DateTimeFormatter WRITTEN = DateTimeFormatter.ofPattern("HH:mm:ss");

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

    /** The time of day {@code count} counts to, written the way a model writes one. A count
     * carrying a fraction is floored rather than written as a time no model could have named, which
     * is the answer {@link DateTimes#written} gives for the same reason. */
    public static String written(Place count) {
        return written(LocalTime.ofSecondOfDay(Count.number(count).at()
                .setScale(0, RoundingMode.FLOOR).longValueExact()));
    }

    /** The same text, for a caller holding the value rather than the count. Every place a time of
     * day is written down goes through here, so a line's label and the value a report says came
     * back are the same text for the same value. */
    public static String written(LocalTime at) {
        return at.format(WRITTEN);
    }

    private Times() {}
}
