package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
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
 * <p>Equality is the records' own, and is not the order for a level on a carrier: {@code 0} and
 * {@code 0.00} are two values there and one level, which is what {@link Place#key()} is for and what
 * every comparison in the algebra goes through instead. A reader that has to put a level inside
 * something compared as a value holds {@link #canonical()}.
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
     *
     * <p><b>An exact ratio and not a {@link Count}.</b> A count is the number a value counts to
     * <em>on</em> a carrier's order, and every carrier's order is counted in decimals. What a
     * quantity counts to is on no such order: a form weighed by a third takes the values a third
     * apart, and the lattice itself is then over a number no decimal writes. The two shared a
     * representation only while every level a form could take was a finite decimal, and a level held
     * as a count would round the moment the arithmetic left them.
     */
    record OfTheQuantity(ExactRatio at) implements Level {

        public OfTheQuantity {
            if (at == null) {
                throw new IllegalArgumentException("a counted level is a number");
            }
        }

        public static OfTheQuantity of(long n) {
            return new OfTheQuantity(ExactRatio.of(n));
        }

        @Override
        public String toString() {
            return at.toString();
        }
    }

    /** The one level where two positions meet, which every quantity of a distance has. */
    Level WHERE_THEY_MEET = new OfTheQuantity(ExactRatio.ZERO);

    /**
     * This level as the exact number it is.
     *
     * <p>Only where it is one. A level on a carrier is a value of that carrier and may be a string,
     * and a caller that has established it is holding a number — a distance, or what a form comes to
     * — is holding one of these. The narrowing is here so that it is one line to find rather than a
     * cast written wherever a number was wanted.
     */
    default ExactRatio asAnExactNumber() {
        if (!(this instanceof OfTheQuantity counted)) {
            throw new IllegalStateException("a level that is not a number was asked for one: " + this);
        }
        return counted.at();
    }

    /**
     * This level as a place on the order it is a level of.
     *
     * <p>The carrier edge for a level, and the one of them: a place on a carrier is already one, and
     * a number the quantity counts to is a place exactly where a carrier's order could count to it
     * ({@link Count#at}). Written out at each reader instead, four of them had the same two lines
     * and none of them said what happens to a number no order counts to.
     *
     * <p>Refused rather than answered with a rounding, which is {@link Count#number(ExactRatio)}'s
     * to say. Every caller here is holding a level it has established is a place — an end of a run
     * on a carrier, a line a place is compared against — and a level at a third reaching one of them
     * is this compiler having mixed two orders. A reader that means to ask whether a line is a value
     * of something asks {@link CutPosition#asAValueOf}, which answers.
     */
    default Place asAPlace() {
        return switch (this) {
            case OnACarrier on -> on.at();
            case OfTheQuantity(ExactRatio at) -> Count.number(at);
        };
    }

    /**
     * The same distance measured the other way round.
     *
     * <p>For a quantity that is how far two positions stand apart, which is the one kind of level
     * there is a second way to read. {@code a - b} and {@code b - a} are one relation and two
     * quantities, and a reader holding a demand about the first reads it about the second by
     * negating every level in it — which is what lets either position be the one a search settles
     * ({@link Criterion#reflected()}).
     *
     * <p>Refused for a level that is not a number. A value of a carrier is a value of a position and
     * not a distance between two of them, so there is nothing for the other way round to mean.
     */
    default Level negated() {
        return switch (this) {
            case OfTheQuantity(ExactRatio at) -> new OfTheQuantity(at.negated());
            case OnACarrier(Carrier of, Place at) -> {
                if (!(at instanceof Count count)) {
                    throw new IllegalStateException(
                            "an order with no numbers has no distance to read the other way round: "
                                    + this);
                }
                yield new OnACarrier(of, count.negate());
            }
        };
    }

    /** What makes two levels one level: what they are, and not how the number was written. The same
     *  rule {@link Place#key()} states, asked of a level so that a reader holding one never reaches
     *  past it for the place inside. An exact ratio is in lowest terms already, so it is its own
     *  key. */
    default String key() {
        return switch (this) {
            case OnACarrier on -> on.at().key();
            case OfTheQuantity counted -> counted.at().toString();
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
            // An exact ratio is kept in lowest terms by the type, so two writings of one number are
            // already one value and there is nothing here to spell again.
            case OfTheQuantity counted -> counted;
            case OnACarrier(Carrier of, Place at) -> new OnACarrier(of, at.canonical());
        };
    }
}
