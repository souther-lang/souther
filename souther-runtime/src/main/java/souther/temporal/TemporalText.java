package souther.temporal;

import java.time.DateTimeException;
import java.time.Instant;
import java.time.LocalDate;
import java.time.LocalTime;
import java.time.Year;
import java.time.ZoneOffset;
import java.time.format.DateTimeFormatter;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Which text names a {@code Date}, a {@code Time}, a {@code DateTime} or an {@code Instant}
 * (spec {@code [#temporal-text]}).
 *
 * <p>Each form is a regular expression over ASCII, and that expression alone decides whether a text
 * is in the form. {@code java.time} is asked afterwards whether the fields name a day and a moment
 * that exist; it never decides the grammar. Its parsers take lower-case {@code t} and {@code z},
 * and a decimal point with no digits after it, so a text a caller may write would otherwise depend
 * on the JDK's leniency and on the version of whatever library hands the text to it.
 *
 * <p>This is the language's and not a backend's, so the checker reads it for a written temporal and
 * a backend reads it for a text that arrives, and they are the same question. It has no part in
 * any one target's classes.
 *
 * <p>Two languages are read here. What a boundary takes is {@link #atBoundary}. What source may
 * write is {@link #inSource}, which is the boundary's language with one more condition: an
 * {@code Instant} is written in UTC. A text the boundary refuses is refused in source, so the
 * language a program writes is inside the language a program reads. An offset is a spelling and not
 * a zone: it is a displacement from UTC that names the same moment as the {@code Z} form of it, and
 * source writes the {@code Z} form because a value is written the way it is written back.
 *
 * <p>The refusal is the reason and not a flag, because the reasons are different things to tell a
 * caller: text that is no temporal, text that carries a fraction of a second the type cannot hold,
 * text that names a leap second, and (in source) an offset that is not {@code Z}.
 */
public final class TemporalText {

    /** The four temporals that have a text form. */
    public enum Kind { DATE, TIME, DATETIME, INSTANT }

    /** Why a text is not one. */
    public enum Refusal {
        /** Not in the form, or in it and naming no day or moment. */
        MALFORMED,
        /** A {@code Time} or {@code DateTime} written with a fraction of a second, even a zero one. */
        SUB_SECOND,
        /** An {@code Instant} whose second is 60. */
        LEAP_SECOND,
        /** An {@code Instant} in source whose offset is not {@code Z}. */
        NOT_UTC
    }

    // Four digits and no sign for 0000 to 9999; otherwise a sign, and no leading zero beyond the
    // four-digit minimum. "-0000" is not year 0.
    private static final String YEAR =
            "(?<year>[0-9]{4}|\\+[1-9][0-9]{4,9}|-(?!0000)[0-9]{4}|-[1-9][0-9]{4,9})";
    private static final String DATE = YEAR + "-(?<month>[0-9]{2})-(?<day>[0-9]{2})";
    private static final String HOUR_MINUTE = "(?<hour>[0-9]{2}):(?<minute>[0-9]{2})";
    // A fraction has one to nine digits. A point with none after it is not a fraction.
    private static final String SECOND = ":(?<second>[0-9]{2})(?:\\.(?<fraction>[0-9]{1,9}))?";
    private static final String TIME = HOUR_MINUTE + "(?:" + SECOND + ")?";
    private static final String OFFSET = "(?:(?<utc>Z)|(?<offsetSign>[+-])"
            + "(?<offsetHour>[0-9]{2}):(?<offsetMinute>[0-9]{2})(?::(?<offsetSecond>[0-9]{2}))?)";

    private static final Pattern DATE_FORM = Pattern.compile(DATE);
    private static final Pattern TIME_FORM = Pattern.compile(TIME);
    private static final Pattern DATETIME_FORM = Pattern.compile(DATE + "T" + TIME);
    // An instant requires its seconds.
    private static final Pattern INSTANT_FORM =
            Pattern.compile(DATE + "T" + HOUR_MINUTE + SECOND + OFFSET);

    private TemporalText() {}

    /** Why {@code text} is not a {@code kind} at a boundary, or empty where it is one. */
    public static Optional<Refusal> atBoundary(Kind kind, String text) {
        return switch (kind) {
            case DATE -> {
                Matcher m = DATE_FORM.matcher(text);
                yield m.matches() && dateExists(m) ? none() : malformed();
            }
            case TIME -> local(TIME_FORM.matcher(text), false);
            case DATETIME -> local(DATETIME_FORM.matcher(text), true);
            case INSTANT -> instant(INSTANT_FORM.matcher(text), text);
        };
    }

    /** Why {@code text} is not a {@code kind} as source writes it, or empty where it is one. */
    public static Optional<Refusal> inSource(Kind kind, String text) {
        Optional<Refusal> refused = atBoundary(kind, text);
        if (refused.isPresent()) {
            return refused;
        }
        return kind == Kind.INSTANT && !text.endsWith("Z")
                ? Optional.of(Refusal.NOT_UTC) : none();
    }

    /** What a refusal says the text does, worded once so that every reader of the language reports
     *  the same thing. */
    public static String says(Kind kind, Refusal refusal) {
        return switch (refusal) {
            case MALFORMED -> switch (kind) {
                case DATE -> "is not a Date written as yyyy-MM-dd";
                case TIME -> "is not a Time written as HH:mm or HH:mm:ss";
                case DATETIME ->
                        "is not a DateTime written as yyyy-MM-ddTHH:mm or yyyy-MM-ddTHH:mm:ss";
                case INSTANT -> "is not an Instant written as yyyy-MM-ddTHH:mm:ss with an offset";
            };
            case SUB_SECOND -> "holds no fraction of a second";
            case LEAP_SECOND -> "names a leap second, which is no moment here";
            case NOT_UTC -> "is not written in UTC";
        };
    }

    /**
     * The question a decoder asks of a text before it parses one, as a predicate over what the
     * decoder is handed. With {@code only} empty it asks whether the text is a {@code kind} at all;
     * with a reason it asks whether that is <em>not</em> the reason the text is refused for, so a
     * decoder can put the reasons in the order it reports them. Anything that is not a
     * {@code String} is not text and is not this question's concern, so it holds.
     */
    public static boolean holds(Object text, Kind kind, Optional<Refusal> only) {
        if (!(text instanceof String s)) {
            return true;
        }
        Optional<Refusal> refused = atBoundary(kind, s);
        return only.isEmpty() ? refused.isEmpty() : !refused.equals(only);
    }

    private static Optional<Refusal> local(Matcher m, boolean withDate) {
        if (!m.matches() || withDate && !dateExists(m) || !timeExists(m)) {
            return malformed();
        }
        return m.group("fraction") == null ? none() : Optional.of(Refusal.SUB_SECOND);
    }

    private static Optional<Refusal> instant(Matcher m, String text) {
        if (!m.matches() || !dateExists(m) || !offsetExists(m)) {
            return malformed();
        }
        if (m.group("second").equals("60")) {
            // A second that does not exist. Which hour and minute it is said at is checked as the
            // rest of the moment would be, with the second the JDK can hold.
            return timeExists(m, 59) ? Optional.of(Refusal.LEAP_SECOND) : malformed();
        }
        try {
            // The form decided the grammar. ISO_INSTANT only builds the value: it is the JDK's
            // constructor for the whole Instant range, whose years LocalDate cannot hold, and it
            // reads 24:00:00 as the start of the next day.
            Instant.from(DateTimeFormatter.ISO_INSTANT.parse(text));
            return none();
        } catch (DateTimeException _) {
            return malformed();
        }
    }

    private static boolean dateExists(Matcher m) {
        long year = Long.parseLong(m.group("year"));
        if (year < Year.MIN_VALUE || year > Year.MAX_VALUE) {
            return false;
        }
        try {
            LocalDate.of((int) year, Integer.parseInt(m.group("month")), Integer.parseInt(m.group("day")));
            return true;
        } catch (DateTimeException _) {
            return false;
        }
    }

    private static boolean timeExists(Matcher m) {
        String second = m.group("second");
        return timeExists(m, second == null ? 0 : Integer.parseInt(second));
    }

    private static boolean timeExists(Matcher m, int second) {
        try {
            LocalTime.of(Integer.parseInt(m.group("hour")), Integer.parseInt(m.group("minute")), second);
            return true;
        } catch (DateTimeException _) {
            return false;
        }
    }

    private static boolean offsetExists(Matcher m) {
        if (m.group("utc") != null) {
            return true;
        }
        int sign = "-".equals(m.group("offsetSign")) ? -1 : 1;
        String second = m.group("offsetSecond");
        try {
            ZoneOffset.ofHoursMinutesSeconds(
                    sign * Integer.parseInt(m.group("offsetHour")),
                    sign * Integer.parseInt(m.group("offsetMinute")),
                    sign * (second == null ? 0 : Integer.parseInt(second)));
            return true;
        } catch (DateTimeException _) {
            return false;
        }
    }

    private static Optional<Refusal> none() {
        return Optional.empty();
    }

    private static Optional<Refusal> malformed() {
        return Optional.of(Refusal.MALFORMED);
    }
}
