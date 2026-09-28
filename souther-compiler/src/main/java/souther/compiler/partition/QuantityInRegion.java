package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;

import java.util.Set;

/**
 * A border's quantity standing somewhere, which is what a row at one of its items has to do.
 *
 * <p>Said of the quantity and not of the positions it is taken of, because that is what the item
 * says. How far two positions stand apart lying between two lines is one statement about the pair:
 * either of them may take any number the other leaves room for, and a reader that wrote the item
 * down against each of them would have a row standing at a distance at each end of it.
 *
 * <p><b>The item's own values, carried as they are.</b> What a row's number has to be is a
 * {@link LevelRegion} already — runs, and the values a rule singles out taken out of them — so it
 * travels as one. Written out as comparisons instead, a value held away from would come back as a
 * pair of ends and the item would be wider here than the rule that drew it.
 *
 * @param quantity what the row's number is taken of
 * @param values   where that number has to stand
 */
public record QuantityInRegion(BorderQuantity quantity, LevelRegion values)
        implements JointDemand {

    public QuantityInRegion {
        if (quantity == null || values == null) {
            throw new IllegalArgumentException(
                    "a quantity standing somewhere is a quantity and where: " + quantity);
        }
    }

    @Override
    public Set<NumericTerm> terms() {
        return Set.copyOf(quantity.terms());
    }
}
