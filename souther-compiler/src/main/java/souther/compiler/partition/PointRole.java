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

    /**
     * Which of the four a point of a border is, from the two questions that tell them apart.
     *
     * <p>Derived and never chosen. Where the point is says whether it is against the line, and the
     * rule says whether it holds there; the four are the pairs. Assigned by hand wherever a border
     * is built, the same two facts are read into a role by a switch per shape of line, and a role is
     * what everything downstream reports and counts.
     *
     * @param holdsThere whether the rule that drew the line is satisfied by a row at this point
     */
    public static PointRole of(DomainPoint point, boolean holdsThere) {
        if (point.againstTheLine()) {
            return holdsThere ? ON : OFF;
        }
        return holdsThere ? IN : OUT;
    }

    /** Whether a row at this point stands inside the partition the border bounds. */
    public boolean inside() {
        return this == ON || this == IN;
    }

    /** Whether this is one of the two the border names a value for, as against a region. */
    public boolean againstTheLine() {
        return this == ON || this == OFF;
    }
}
