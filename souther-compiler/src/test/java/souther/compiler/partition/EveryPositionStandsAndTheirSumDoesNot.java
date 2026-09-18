package souther.compiler.partition;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.Optional;

/**
 * A region where each position runs somewhere and what they add up to runs nowhere.
 *
 * <p><b>The shape a per-position reading cannot see.</b> What a rule over two positions leaves is a
 * fact about the sum: each of them may stand at any of several values while no pair of those values
 * satisfies the rule. So a reader that asks where each position runs is asking a weaker question
 * than the one a form puts, and every answer it gets back is true.
 *
 * <p>Which is why the projection is of a form and not of an atom carrying a form's name. Asked one
 * position at a time and met with a range each time, a reader learns nothing about the sum and goes
 * on to walk it.
 */
final class EveryPositionStandsAndTheirSumDoesNot implements SearchRegion {

    static final SearchRegion REGION = new EveryPositionStandsAndTheirSumDoesNot();

    @Override
    public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
        return new Assumption.Taken(this);
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
    public PlacesApart apartAt(NumericTerm.FromOnePosition term) {
        return PlacesApart.NONE;
    }

    /**
     * A short run for one position, and nothing for anything that weighs more than one of them.
     *
     * <p>Where a form of one term is the position itself, which is the shape every reader asking
     * about a position uses.
     */
    @Override
    public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
        return form.coefs().size() > 1
                ? new NumericDomain.FormProjection.NothingIsLeft()
                : new NumericDomain.FormProjection.Within(new NumericDomain.Bounds(
                        Endpoint.inclusive(Count.of(0)), Endpoint.inclusive(Count.of(2))));
    }

    /** Nothing shows the region empty: what contradicts is the sum, and the rules that say so are
     *  not ones this proves anything from on its own. */
    @Override
    public Optional<EmptyInput> emptiness() {
        return Optional.empty();
    }

    private EveryPositionStandsAndTheirSumDoesNot() {}
}
