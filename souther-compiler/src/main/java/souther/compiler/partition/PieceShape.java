package souther.compiler.partition;

/**
 * What one place of a string made for a body's demand is, and which string it is a string of.
 *
 * <p>A string the body parts is two strings: the one the input holds, and the one the body's case
 * conversions make of it, which is what is parted, what the newtype is built of and what the other
 * inputs are looked up against. Which of the two a value is a value of is part of what the value
 * is, so a place says it, and whoever puts a string together from places takes each to the
 * language of the input by the one reading of it ({@code Partitions#stringsPartedInto}) rather than
 * by remembering which of its strings were which.
 */
sealed interface PieceShape {

    /** The piece as it was seen: a string of the input, kept as it was written. */
    record AsSeen(String written) implements PieceShape {
    }

    /** Any string the newtype admits, once the conversions have been made: a string of the input
     *  that is made into one. */
    record AnyTheTypeAdmits() implements PieceShape {
    }

    /** Exactly this string, once the conversions have been made: a string of the input that is
     *  made into it. */
    record MadeInto(String converted) implements PieceShape {
    }
}
