package souther.compiler.inputs;

import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.ValueName;

import java.util.Objects;

/**
 * Where the rules reaching a container leave a number an operation accumulates over what its
 * elements hold at one place.
 *
 * <p>Said at the place each element's value stands, {@code lines[*].amount}, which is where a body
 * reads the same total from ({@link RunSource.ProjectedOccurrences}). What a rule called the
 * container is translated to the position once, where the rules are placed ({@link PlacedRules}),
 * so a reader of this compares places and makes no name.
 *
 * @param place where each element's value stands: the element itself where the elements are what
 *              is added up
 */
public record TotalLeft(ValueName operation, TermPath place, NumericDomain.Bounds left) {

    public TotalLeft {
        Objects.requireNonNull(operation, "a total is taken by some operation");
        Objects.requireNonNull(place, "over what stands at some place");
        Objects.requireNonNull(left, "and the rules leave it somewhere");
    }
}
