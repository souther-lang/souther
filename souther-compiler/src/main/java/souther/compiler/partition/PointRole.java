package souther.compiler.partition;

/**
 * One of the four coverage items a border owes, in the words domain testing gives them.
 *
 * <p>Keyed on the border and on nothing else. Two of these used to be answered here and two by the
 * measure that counts the classes a position is divided into — which answers "is some row in this
 * partition" and not "does this border have an {@code IN} point", and has no word at all for a row on
 * the far side of a line. One technique's four items were counted under two units, and only one of
 * the two could be said about a border.
 *
 * <p>What tells them apart is two questions and not one. {@code ON} and {@code OFF} are the two
 * values against the line, and which of them the line's own value is turns on whether the border is
 * closed — the same {@code AT} is the {@code ON} point of {@code <= 3000} and the {@code OFF} point
 * of {@code < 3000}. {@code IN} and {@code OUT} are not values at all: they are the two sides, away
 * from the line, and a row is at one of them by landing in a region rather than by writing a place.
 * A reader that had the second for the first would ask for a representative value and call every
 * other row in the region uncovered.
 */
public enum PointRole {

    /** Inside the partition the border bounds, and closest to the border. */
    ON,

    /** Outside it, and closest to the border. */
    OFF,

    /** Inside it and away from the border, which is what tells this from {@link #ON}. */
    IN,

    /** Outside it and away from the border, likewise against {@link #OFF}. */
    OUT;

    /** Whether a row at this point stands inside the partition the border bounds. */
    public boolean inside() {
        return this == ON || this == IN;
    }

    /** Whether this is one of the two the border names a value for, as against a region. */
    public boolean againstTheLine() {
        return this == ON || this == OFF;
    }
}
