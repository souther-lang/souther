package souther.compiler.partition;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.Optional;

/**
 * A region that stands, with one position in it that the rules leave nowhere.
 *
 * <p><b>The pair a check about this has to be built from.</b> A region proved empty answers both
 * questions the same way, so a reader that asked either of them would pass — and the two are not one
 * question. An input holding an empty collection is a value, and every position inside that
 * collection is a position no row writes anything at: the whole stands and the part has nothing.
 *
 * <p>Narrowing is where the second question is asked again. Fixing a position hands the search a
 * region it has not asked anything of yet, and a position that had somewhere to stand in the region
 * the search was handed may have nowhere in that one. So this also answers as itself after a fixing,
 * which is what puts a walk rather than an entry in front of the question.
 */
final class OnePositionTheRulesLeaveNothing implements SearchRegion {

    private final NumericTerm left;

    /** A region where {@code left} has nowhere to stand and everything else runs unbounded. */
    static SearchRegion leaving(NumericTerm left) {
        return new OnePositionTheRulesLeaveNothing(left);
    }

    private OnePositionTheRulesLeaveNothing(NumericTerm left) {
        this.left = left;
    }

    @Override
    public SearchRegion assuming(LinearForm<NumericTerm> form, Rel rel) {
        return this;
    }

    @Override
    public SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel) {
        return this;
    }

    @Override
    public SearchRegion given(Map<NumericTerm, Place> fixed) {
        return this;
    }

    @Override
    public SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at) {
        return this;
    }

    @Override
    public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
        return form.coefs().containsKey(left)
                ? new NumericDomain.FormProjection.NothingIsLeft()
                : new NumericDomain.FormProjection.Within(NumericDomain.Bounds.OPEN);
    }

    /** Nothing proved the region empty, which is the whole point of it. */
    @Override
    public Optional<EmptyInput> emptiness() {
        return Optional.empty();
    }
}
