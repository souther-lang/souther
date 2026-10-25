package souther.compiler.numeric;

import java.util.Objects;

/**
 * What a numeric type says of an atom's values: how they are spaced, and where the order they are
 * counted on stops.
 *
 * <p>One value, because the two are facts about the same position and a domain told one without
 * the other answers about values no row holds. It is the only thing a domain is told of an atom,
 * so no route can carry the spacing and leave the ends behind.
 *
 * <p>Where the order stops is {@link Extent.Stops} when the type said, with
 * {@link NumericDomain.Bounds#OPEN} for an order that has no end, and {@link Extent.Untold} when
 * nothing said — an atom no type could be found for. An untold extent is not an open one: a
 * system with an atom whose extent is untold is not shown to leave a row, where an open one is
 * shown to leave whatever its rules leave.
 *
 * @param spacing how the values are spaced
 * @param extent  where the order stops. Not a rule: it says which points of the rules a row can be
 */
public record NumberSpace(Granularity spacing, Extent extent) {

    public NumberSpace {
        Objects.requireNonNull(spacing);
        Objects.requireNonNull(extent);
    }

    /** Where an order stops, as far as anything said. */
    public sealed interface Extent {

        /** The ends a type gave its order. */
        record Stops(NumericDomain.Bounds bounds) implements Extent {

            public Stops {
                Objects.requireNonNull(bounds);
            }
        }

        /** Nothing said where the order stops. */
        enum Untold implements Extent {
            UNTOLD
        }
    }

    /** The space of an atom whose order stops at {@code bounds}. */
    public static NumberSpace stopping(Granularity spacing, NumericDomain.Bounds bounds) {
        return new NumberSpace(spacing, new Extent.Stops(bounds));
    }

    /** The space of an atom no type was found for: spaced, and with nothing said of its ends. */
    public static NumberSpace spacedOnly(Granularity spacing) {
        return new NumberSpace(spacing, Extent.Untold.UNTOLD);
    }

    /** Where the order stops, or null where nothing said. */
    public NumericDomain.Bounds stops() {
        return extent instanceof Extent.Stops(NumericDomain.Bounds bounds) ? bounds : null;
    }

    /**
     * What two tellings of one atom come to: the one where they are alike, and the one that said
     * where the order stops where the other did not.
     *
     * <p>Two spacings, or two ends, under one atom are the naming and the typing disagreeing, and
     * the answer to that is to stop rather than to pick the safer of the two.
     *
     * @throws IllegalStateException where the two disagree
     */
    public NumberSpace joinedWith(NumberSpace other) {
        if (spacing != other.spacing) {
            throw new IllegalStateException("is " + spacing + " and " + other.spacing);
        }
        if (extent.equals(other.extent)) {
            return this;
        }
        if (extent == Extent.Untold.UNTOLD) {
            return other;
        }
        if (other.extent == Extent.Untold.UNTOLD) {
            return this;
        }
        throw new IllegalStateException("stops at " + stops() + " and " + other.stops());
    }
}
