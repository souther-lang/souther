package souther.compiler.partition;

import java.math.BigDecimal;
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
final class Dates {

    /** The day {@code iso} is, or null where it is not a date this reads. */
    static BigDecimal dayOf(String iso) {
        if (iso == null || iso.indexOf('T') >= 0) {
            return null;   // a date-time, whose step is not a day
        }
        try {
            return BigDecimal.valueOf(LocalDate.parse(iso).toEpochDay());
        } catch (DateTimeParseException _) {
            return null;
        }
    }

    /** The date {@code day} counts to, written the way a model writes one. */
    static String written(BigDecimal day) {
        return LocalDate.ofEpochDay(day.longValueExact()).toString();
    }

    private Dates() {}
}
