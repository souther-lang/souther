package souther.compiler.numeric;

import java.math.RoundingMode;
import java.time.LocalDateTime;
import java.time.ZoneOffset;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;

/**
 * A date-time as the interval algebra can hold it, and back again.
 *
 * <p>Counting seconds from an epoch is order-preserving, so the ranges and the representative are
 * the ones already written for numbers. The offset is fixed at UTC and is not a claim about a zone:
 * a {@code DateTime} carries none (spec §primitives), and what the count is for is comparing two of
 * them, which any fixed offset answers the same way.
 *
 * <p><b>Seconds and not days, and this is why the two are separate carriers.</b> One carrier cannot
 * be both without a line drawn on a day standing beside one drawn on a second with nothing saying
 * which was which (ADR-0090). Which of the two a value is on is decided by its declared type, and
 * the texts do not overlap — a date-time is written with its time and a date is not — so a reader
 * handed a written temporal can tell them apart, and {@link Dates#dayOf} and {@link #secondOf} each
 * decline the other's.
 *
 * <p><b>The adjacent value is a second away.</b> This once said a date-time had no smallest step the
 * language named, and that whether the value beside a cut-over was a second, a millisecond or a
 * nanosecond earlier was a decision nobody had taken. It has since been taken: a {@code DateTime} is
 * held to the second (spec §a-local-temporal-is-held-to-the-second), so the second either side of a
 * line is a date-time and is named. The counts are therefore whole, as day counts are in
 * {@link Dates}, and a count with a fraction is a number and no date-time — which is what the
 * round-trip in {@code Carrier.onTheGrid} asks this to answer.
 */
public final class DateTimes {

    /** Seconds are spelled out even at zero, so the text a boundary is named by is the text a model
     * writes. {@code LocalDateTime.toString} drops them, and a line at midnight would then be
     * printed one way and written another. */
    private static final DateTimeFormatter WRITTEN =
            DateTimeFormatter.ofPattern("uuuu-MM-dd'T'HH:mm:ss");

    /**
     * The first and last counts a date-time can be written as.
     *
     * <p>Where the calendar stops, which is not where the arithmetic does. A count past either is a
     * number and no date-time, and the only reader that may say so is the one that knows the two —
     * so they are named here rather than left to whatever exception the writer happens to throw.
     *
     * <p>Both are whole. {@code LocalDateTime.MAX} carries a fraction of a second that no
     * {@code DateTime} can be written as, so the last one that can is the second it falls in.
     */
    public static final Count MIN = countAt(LocalDateTime.MIN);

    public static final Count MAX = countAt(LocalDateTime.MAX);

    private static Count countAt(LocalDateTime at) {
        return Count.of(at.toEpochSecond(ZoneOffset.UTC));
    }

    /** Whether {@code count} is one of the counts a date-time can be written as. */
    public static boolean holds(Place count) {
        return count.compareTo(MIN) >= 0 && count.compareTo(MAX) <= 0;
    }

    /** The second {@code iso} counts to, or null where it is not a date-time this reads. A
     * {@code DateTime} holds no fraction of a second, so nothing is carried below it. */
    public static Count secondOf(String iso) {
        if (iso == null || iso.indexOf('T') < 0) {
            return null;   // a date, whose step is a day
        }
        try {
            return Count.of(LocalDateTime.parse(iso).toEpochSecond(ZoneOffset.UTC));
        } catch (DateTimeParseException _) {
            return null;
        }
    }

    /** The date-time {@code count} counts to, written the way a model writes one. A count carrying a
     * fraction is floored rather than written as a date-time no model could have named, which is
     * what lets the round-trip that asks whether this carrier holds a count answer no. */
    public static String written(Place count) {
        return written(LocalDateTime.ofEpochSecond(
                Count.number(count).at().setScale(0, RoundingMode.FLOOR).longValueExact(),
                0, ZoneOffset.UTC));
    }

    /** The same text, for a caller holding the value rather than the count. Every place a date-time
     * is written down goes through here, so a line's label and the value a report says came back
     * are the same text for the same value. */
    public static String written(LocalDateTime at) {
        return at.format(WRITTEN);
    }

    private DateTimes() {}
}
