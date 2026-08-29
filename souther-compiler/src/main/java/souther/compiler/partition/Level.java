package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

/**
 * One value of a {@link BorderQuantity}.
 *
 * <p>Apart from {@link Place}, which is a value of a <em>position</em>. The two are the same thing
 * for a quantity that is a coordinate and are not the same thing for any other: how far apart two
 * positions stand is a number on no position's order, and what an affine form comes to is a number
 * no position holds. Held as one type, a quantity over strings answered with a count and the count
 * was handed to {@link Carrier#written} — a carrier with no numbers asked to write one.
 *
 * <p>Which of the two shapes a level has is the quantity's to say and no reader's to ask. Everything
 * that compares two of them goes through {@link LevelSpace}, which refuses two levels of different
 * spaces the way {@link Place#notOneOrder} refuses two carriers' places.
 *
 * <p>Equality is the records' own, and is not the order. {@code 0} and {@code 0.00} are two values
 * here and one level, which is what {@link Place#key()} is for and what every comparison in the
 * algebra goes through instead. A reader that has to put a level inside something compared as a
 * value holds {@link #canonical()}.
 */
public sealed interface Level {

    /**
     * A value of one coordinate, on the carrier that coordinate is ordered by.
     *
     * <p>The carrier travels with it because writing it back is the carrier's, and because two
     * carriers' places are never compared. A level of this shape is the only one anything may ask a
     * carrier to write.
     */
    record OnACarrier(Carrier of, Place at) implements Level {

        public OnACarrier {
            if (of == null || at == null) {
                throw new IllegalArgumentException("a level on a carrier has both");
            }
        }

        @Override
        public String toString() {
            return at.key();
        }
    }

    /**
     * A number the quantity itself counts to, which is on no coordinate's carrier.
     *
     * <p>How many steps two positions stand apart, and what an affine form comes to. Neither is a
     * value anything holds: a row at either is a row this has to be solved for, which is what
     * {@link Standing} carries and {@link LevelRealizer} answers.
     */
    record ACount(Count at) implements Level {

        public ACount {
            if (at == null) {
                throw new IllegalArgumentException("a counted level is a number");
            }
        }

        public static ACount of(long n) {
            return new ACount(Count.of(n));
        }

        @Override
        public String toString() {
            return at.key();
        }
    }

    /**
     * This level as the number it is.
     *
     * <p>Only where it is one. A level on a carrier is a value of that carrier and may be a string,
     * and a caller that has established it is holding a number — a distance, or what a form comes to
     * — is holding one of these. The narrowing is here so that it is one line to find rather than a
     * cast written wherever a number was wanted.
     */
    default Count asACount() {
        if (!(this instanceof ACount count)) {
            throw new IllegalStateException("a level that is not a number was asked for one: " + this);
        }
        return count.at();
    }

    /** What makes two levels one level: what they are, and not how the number was written. The same
     *  rule {@link Place#key()} states, asked of a level so that a reader holding one never reaches
     *  past it for the place inside. */
    default String key() {
        return switch (this) {
            case OnACarrier on -> on.at().key();
            case ACount count -> count.at().key();
        };
    }

    /**
     * This level with its place spelled the one way, for an identity to be built from.
     *
     * <p>{@link #key()} answers the same question and answers it about the place alone: a level of a
     * carrier and a number the quantity counts to have the same key where the number is the same,
     * and they are not one level. So a value that holds a level and is compared as a value holds
     * this rather than that.
     */
    default Level canonical() {
        return switch (this) {
            case OnACarrier(Carrier of, Place at) -> new OnACarrier(of, at.canonical());
            case ACount(Count at) -> new ACount(at.canonical());
        };
    }
}
