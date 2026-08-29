package souther.compiler.numeric;

import java.time.LocalDate;
import java.time.format.DateTimeParseException;

/**
 * A date as the interval algebra can hold it, and back again.
 *
 * <p>A date is a discrete total order, which is everything a line drawn on it needs: two dates
 * compare, and either has the one beside it. Counting days from an epoch is order-preserving, so the
 * ranges, the neighbours and the representative are the ones already written for whole numbers, and
 * nothing about dates is written twice.
 *
 * <p>The count is a carrier and never an answer. Every value that leaves the algebra — a cut, a
 * boundary, a generated fixture — is a date again, because a day number is not something a model
 * says or a person writes. That conversion is here and in one direction each way, so a report cannot
 * disagree with a fixture about what a line is drawn at.
 *
 * <p>Dates only, not date-times. A time carries a finer step whose size is a separate decision, and
 * mixing the two units in one carrier would put a line drawn on a day beside one drawn on a second
 * with nothing saying which was which. A date-time comparison is left unread, which is said as that.
 */
public final class Dates {

    /** The day {@code iso} counts to, or null where it is not a date this reads. */
    public static Count dayOf(String iso) {
        if (iso == null || iso.indexOf('T') >= 0) {
            return null;   // a date-time, whose step is not a day
        }
        try {
            return dayOf(LocalDate.parse(iso));
        } catch (DateTimeParseException _) {
            return null;
        }
    }

    /** The day {@code date} counts to. */
    public static Count dayOf(LocalDate date) {
        return Count.of(date.toEpochDay());
    }

    /**
     * The date {@code day} counts to.
     *
     * <p>The one place a count becomes a calendar again, as {@link #dayOf} is the one place a
     * calendar becomes a count. What a date is written as and what parts it has are both read off
     * this, so a report and a fixture cannot come to different dates from the same day.
     */
    public static LocalDate dateAt(Place day) {
        return LocalDate.ofEpochDay(Count.number(day).at().longValueExact());
    }

    /** The date {@code day} counts to, written the way a model writes one. */
    public static String written(Place day) {
        return dateAt(day).toString();
    }

    private Dates() {}
}
