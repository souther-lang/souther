package souther.compiler.numeric;

import java.util.Objects;

/**
 * How the value a number is taken of was derived from the one standing at a position.
 *
 * <p>Not part of what is taken. {@code Date.year} takes the year of whatever date it is given, and
 * what differs between the year of {@code b} and the year of {@code Date.addDays(-1, b)} is the
 * date it is given. Kept apart from the operation's arguments, which are the values the operation
 * itself was handed beside the one it takes its number of.
 *
 * <p>Only what has a meaning that composes and an answer to which positions it can be written back
 * to: nothing and a shift of a date. A transformation of another kind is one more arm, and every
 * reader stops compiling until it says what it does with it.
 */
public sealed interface ValueTransformation {

    /** The value at the position, as it stands. */
    ValueTransformation NONE = new Identity();

    /** The transformation of {@code translation}, which is none where it moves nothing anywhere. */
    static ValueTransformation of(DateTranslation translation) {
        Objects.requireNonNull(translation, "a shift of a date says what it shifts by");
        return translation.isNone() ? NONE : new DateShift(translation);
    }

    /** The value at the position. */
    record Identity() implements ValueTransformation {
    }

    /** The date at the position, moved by days and defined where the translation says. */
    record DateShift(DateTranslation translation) implements ValueTransformation {

        public DateShift {
            Objects.requireNonNull(translation, "a shift of a date says what it shifts by");
            if (translation.isNone()) {
                throw new IllegalArgumentException(
                        "a shift that moves nothing anywhere is the identity, which is NONE");
            }
        }
    }

    /** The translation this is, which is none where the value is taken as it stands. */
    default DateTranslation translation() {
        return switch (this) {
            case Identity _ -> DateTranslation.none();
            case DateShift shift -> shift.translation();
        };
    }

    /** {@code value} as it is written where it has been transformed by this. */
    default String writtenAround(String value) {
        return switch (this) {
            case Identity _ -> value;
            case DateShift shift -> "(" + value + " " + shift.translation() + ")";
        };
    }
}
