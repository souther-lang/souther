package souther.temporal;

import net.unit8.notation199x.TemporalText;

import java.util.Optional;

/**
 * Which text names a {@code Date}, a {@code Time}, a {@code DateTime} or an {@code Instant} in
 * Souther (spec {@code [#temporal-text]}).
 *
 * <p>Whether a text is in a temporal's form, and whether its fields name a day and a moment that
 * exist, is the grammar Souther shares with Raoh, and {@link TemporalText} answers it. What is
 * Souther's is what its types hold: a {@code Time} and a {@code DateTime} hold no fraction of a
 * second, which the shared grammar admits. So that is refused here, of text the grammar already
 * took, and a text is in the grammar's language before it is asked about its fraction.
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
public final class TemporalForms {

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

    private TemporalForms() {}

    /** Why {@code text} is not a {@code kind} at a boundary, or empty where it is one. */
    public static Optional<Refusal> atBoundary(Kind kind, String text) {
        Optional<TemporalText.Refusal> refused = TemporalText.refusal(shared(kind), text);
        if (refused.isPresent()) {
            return Optional.of(switch (refused.get()) {
                case MALFORMED -> Refusal.MALFORMED;
                case LEAP_SECOND -> Refusal.LEAP_SECOND;
            });
        }
        // Text the grammar admits holds a full stop only before a fraction of a second.
        return holdsTheSecondAlone(kind) && text.indexOf('.') >= 0
                ? Optional.of(Refusal.SUB_SECOND) : Optional.empty();
    }

    /** Why {@code text} is not a {@code kind} as source writes it, or empty where it is one. */
    public static Optional<Refusal> inSource(Kind kind, String text) {
        Optional<Refusal> refused = atBoundary(kind, text);
        if (refused.isPresent()) {
            return refused;
        }
        return kind == Kind.INSTANT && !text.endsWith("Z")
                ? Optional.of(Refusal.NOT_UTC) : Optional.empty();
    }

    /** What a refusal says the text does, worded once so that every reader of the language reports
     *  the same thing. */
    public static String says(Kind kind, Refusal refusal) {
        return switch (refusal) {
            case MALFORMED -> switch (kind) {
                case DATE -> "is not a Date written as yyyy-MM-dd, its year signed outside 0000 to 9999";
                case TIME -> "is not a Time written as HH:mm or HH:mm:ss";
                case DATETIME -> "is not a DateTime written as yyyy-MM-ddTHH:mm or yyyy-MM-ddTHH:mm:ss,"
                        + " its year signed outside 0000 to 9999";
                case INSTANT -> "is not an Instant written as yyyy-MM-ddTHH:mm:ss with an offset,"
                        + " its year signed outside 0000 to 9999";
            };
            case SUB_SECOND -> "holds no fraction of a second";
            case LEAP_SECOND -> "names a leap second, which is no moment here";
            case NOT_UTC -> "is not written in UTC";
        };
    }

    /** The shared grammar's name for {@code kind}. A date-time with an offset is not a Souther type
     *  and has none. */
    private static TemporalText.Kind shared(Kind kind) {
        return switch (kind) {
            case DATE -> TemporalText.Kind.DATE;
            case TIME -> TemporalText.Kind.TIME;
            case DATETIME -> TemporalText.Kind.DATETIME;
            case INSTANT -> TemporalText.Kind.INSTANT;
        };
    }

    /** Whether a {@code kind} is held to the second, so that a fraction the grammar admits is not
     *  one of its values. An {@code Instant} holds one. */
    private static boolean holdsTheSecondAlone(Kind kind) {
        return switch (kind) {
            case TIME, DATETIME -> true;
            case DATE, INSTANT -> false;
        };
    }
}
