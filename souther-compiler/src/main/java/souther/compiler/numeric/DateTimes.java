package souther.compiler.numeric;

import java.math.BigDecimal;
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
 * <p><b>No adjacent value.</b> A date-time has no smallest step this language names: whether the
 * value beside a cut-over is a second, a millisecond or a nanosecond earlier is a decision nobody
 * has taken, so none is invented and the boundary beside one is reported as not derivable — the
 * same answer a {@code Decimal} gets, and for the same reason. What is between two of them is a
 * different question and has an answer, which is what lets a class still offer a row.
 */
public final class DateTimes {

    /** Seconds are spelled out even at zero, so the text a boundary is named by is the text a model
     * writes. {@code LocalDateTime.toString} drops them, and a line at midnight would then be
     * printed one way and written another. */
    private static final DateTimeFormatter WRITTEN =
            DateTimeFormatter.ofPattern("uuuu-MM-dd'T'HH:mm:ss");

    private static final BigDecimal NANOS = BigDecimal.valueOf(1_000_000_000L);

    /** The second {@code iso} counts to, or null where it is not a date-time this reads. */
    public static Count secondOf(String iso) {
        if (iso == null || iso.indexOf('T') < 0) {
            return null;   // a date, whose step is a day
        }
        try {
            LocalDateTime at = LocalDateTime.parse(iso);
            return Count.of(BigDecimal.valueOf(at.toEpochSecond(ZoneOffset.UTC))
                    .add(BigDecimal.valueOf(at.getNano(), 9)));
        } catch (DateTimeParseException _) {
            return null;
        }
    }

    /** The date-time {@code count} counts to, written the way a model writes one. */
    public static String written(Count count) {
        BigDecimal second = count.at();
        BigDecimal whole = second.setScale(0, RoundingMode.FLOOR);
        BigDecimal fraction = second.subtract(whole).multiply(NANOS)
                .setScale(0, RoundingMode.HALF_UP);
        long seconds = whole.longValueExact();
        long nanos = fraction.longValueExact();
        // Rounding the fraction can reach a whole second; carrying it keeps the value the count says
        // rather than one `LocalDateTime` would refuse.
        if (nanos >= 1_000_000_000L) {
            seconds += 1;
            nanos -= 1_000_000_000L;
        }
        LocalDateTime at = LocalDateTime.ofEpochSecond(seconds, (int) nanos, ZoneOffset.UTC);
        return at.getNano() == 0 ? at.format(WRITTEN) : at.toString();
    }

    private DateTimes() {}
}
