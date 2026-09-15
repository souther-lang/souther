package souther.compiler.inputs;

import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.Optional;

/**
 * A region of one input's values, read off the same rules the input's quantities are read off.
 *
 * <p>One state and two faces. What a region is refined by is a superset of what a reading of the
 * declarations is refined by — a body's conditions as well as a caller's fixings — and the algebra
 * that answers both is the same one, so what differs is which of them each face lets a caller say.
 * Written as two states, a region and the reading it came from could come to disagree about what
 * the declarations leave, which is a disagreement about the model made out of an arrangement of
 * this compiler.
 */
record ReadRegion(ReadQuantities within) implements SearchRegion {

    @Override
    public SearchRegion assuming(LinearForm<NumericTerm> form,
                                 Rel rel) {
        ReadQuantities taken = within.assuming(form, rel);
        return taken == within ? this : new ReadRegion(taken);
    }

    @Override
    public SearchRegion assuming(NumericTerm.FromOnePosition term,
                                 souther.compiler.numeric.Place at, Rel rel) {
        ReadQuantities taken = within.assuming(term, at, rel);
        return taken == within ? this : new ReadRegion(taken);
    }

    @Override
    public SearchRegion apartFrom(NumericTerm.FromOnePosition term,
                                  souther.compiler.numeric.Place at) {
        ReadQuantities taken = within.apartFrom(term, at);
        return taken == within ? this : new ReadRegion(taken);
    }

    @Override
    public SearchRegion given(Map<NumericTerm, souther.compiler.numeric.Place> fixed) {
        ReadQuantities taken = within.fixing(fixed);
        return taken == within ? this : new ReadRegion(taken);
    }

    @Override
    public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
        return within.projectionOf(form);
    }

    @Override
    public Optional<EmptyInput> emptiness() {
        return within.emptiness();
    }
}
