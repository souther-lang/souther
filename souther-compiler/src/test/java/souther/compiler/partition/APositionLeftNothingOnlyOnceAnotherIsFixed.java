package souther.compiler.partition;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.Optional;

/**
 * A region where every position stands until one of them is fixed, after which another has nowhere
 * to be.
 *
 * <p><b>What a gate at the entry cannot cover.</b> A search narrows the region at every value it
 * chooses, so the state an entry check turned away is one the search rebuilds a step later — and
 * the question has to be asked where the narrowing happens rather than once before it. Held here as
 * a region that answers one way to the search that was handed it and another to the walk inside it.
 *
 * <p>The proof this leaves is about the branch and not about the item: the value fixed above is what
 * took the position away, and another value of the same position leaves it standing. Which is why
 * the walk's answer to it is that the branch is exhausted rather than that the model refuses the
 * item — said the second way, one value tried would speak for every value there is.
 */
final class APositionLeftNothingOnlyOnceAnotherIsFixed implements SearchRegion {

    private final NumericTerm first;
    private final NumericTerm second;
    private final boolean fixed;

    /** A region where {@code second} stands until {@code first} is fixed. */
    static SearchRegion of(NumericTerm first, NumericTerm second) {
        return new APositionLeftNothingOnlyOnceAnotherIsFixed(first, second, false);
    }

    private APositionLeftNothingOnlyOnceAnotherIsFixed(NumericTerm first, NumericTerm second,
                                                       boolean fixed) {
        this.first = first;
        this.second = second;
        this.fixed = fixed;
    }

    @Override
    public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
        return new Assumption.Taken(this);
    }

    @Override
    public SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel) {
        return this;
    }

    @Override
    public SearchRegion given(Map<NumericTerm, Place> given) {
        return given.containsKey(first)
                ? new APositionLeftNothingOnlyOnceAnotherIsFixed(first, second, true) : this;
    }

    @Override
    public SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at) {
        return this;
    }

    /**
     * A short run for each position, and nothing at all for the second once the first stands.
     *
     * <p>Short so that a walk of it ends rather than meeting a figure: what is under test is what
     * the walk does with the answer, and a walk that ran out of budget first would come back saying
     * the same thing for a different reason.
     */
    @Override
    public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
        if (fixed && form.coefs().containsKey(second)) {
            return new NumericDomain.FormProjection.NothingIsLeft();
        }
        return new NumericDomain.FormProjection.Within(new NumericDomain.Bounds(
                souther.compiler.numeric.Endpoint.inclusive(Count.of(0)),
                souther.compiler.numeric.Endpoint.inclusive(Count.of(2))));
    }

    /** Nothing ever proves the whole region empty, which is what makes this the case an entry check
     *  misses. */
    @Override
    public Optional<EmptyInput> emptiness() {
        return Optional.empty();
    }
}
