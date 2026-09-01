package souther.compiler.partition;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;

import java.util.Map;
import java.util.Optional;

/**
 * A region that leaves every position a run of a given number of whole numbers.
 *
 * <p>For putting a walk either side of how many values it takes. What a walk that stopped and a
 * walk that reached the end of a run come back with is the same list, so the two are told apart by
 * a run whose width is known and set one either side of the figure.
 *
 * @param many how many whole numbers every position of this region runs over
 */
record ARunOfThisMany(int many) implements SearchRegion {

    @Override
    public SearchRegion assuming(NumericDomain.LinearForm<NumericTerm> form,
                                 NumericDomain.Rel rel) {
        return this;
    }

    @Override
    public SearchRegion given(Map<NumericTerm, Count> fixed) {
        return this;
    }

    /**
     * From nought upward, so that the walk starts inside the run rather than at an end of it.
     *
     * <p>Outward from what it starts at is how the walk goes, so a run from nought to {@code many}
     * gives it {@code many} values above where it starts and none below. Centred instead, the two
     * directions would each hold half and the figure would be reached at twice the width.
     */
    @Override
    public NumericDomain.Bounds runsBetween(NumericDomain.LinearForm<NumericTerm> form) {
        return new NumericDomain.Bounds(new Endpoint(Count.of(0), true),
                new Endpoint(Count.of(many - 1), true));
    }

    @Override
    public Optional<EmptyInput> emptiness() {
        return Optional.empty();
    }
}
