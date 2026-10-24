package souther.compiler.numeric;

import java.util.Objects;

/**
 * What a numeric type says of an atom's values: how they are spaced, and where the order they are
 * counted on stops.
 *
 * <p>One value, because the two are facts about the same position and a domain told one without the
 * other answers about values no row holds. {@link NumericDomain.Bounds#OPEN} is a type whose order
 * has no end, which is something a type says; an atom with no space at all is one the domain was
 * never told of, and is refused rather than read as open.
 *
 * @param spacing how the values are spaced
 * @param extent  where the order stops. Not a rule: it says which points of the rules a row can be
 */
public record NumberSpace(Granularity spacing, NumericDomain.Bounds extent) {

    public NumberSpace {
        Objects.requireNonNull(spacing);
        Objects.requireNonNull(extent);
    }
}
