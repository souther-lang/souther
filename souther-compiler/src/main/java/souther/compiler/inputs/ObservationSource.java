package souther.compiler.inputs;

import souther.compiler.numeric.ValueTransformation;

import java.util.Objects;
import java.util.function.UnaryOperator;

/**
 * The value an operation takes its number of: the one at a position, and what it was turned into
 * before the operation was applied.
 *
 * <p>The position is where a row is asked to hold a value, and the transformation is how the value
 * the operation saw was made of that one. They are one thing to a reader of a number — the year of
 * {@code Date.addDays(-1, b)} is a number of {@code b} — and two to the rest: a boundary is written
 * at the position, and which number it is a boundary of is the transformation's.
 *
 * @param position       where the value the number is derived from stands
 * @param transformation how the value taken of was made of it
 */
public record ObservationSource(TermPath position, ValueTransformation transformation) {

    public ObservationSource {
        Objects.requireNonNull(position, "a number is taken of a value standing somewhere");
        Objects.requireNonNull(transformation,
                "and of what it was made into, which is itself where it was made into nothing");
    }

    /** The value at {@code position}, taken of as it stands. */
    public static ObservationSource asItStands(TermPath position) {
        return new ObservationSource(position, ValueTransformation.NONE);
    }

    /** The same value, standing where {@code moved} puts the position. */
    ObservationSource movedTo(UnaryOperator<TermPath> moved) {
        return new ObservationSource(moved.apply(position), transformation);
    }
}
