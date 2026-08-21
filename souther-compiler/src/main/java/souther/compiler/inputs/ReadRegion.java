package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;

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
    public SearchRegion assuming(NumericDomain.LinearForm<NumericTerm> form,
                                 NumericDomain.Rel rel) {
        ReadQuantities taken = within.assuming(form, rel);
        return taken == within ? this : new ReadRegion(taken);
    }

    @Override
    public SearchRegion given(Map<NumericTerm, Count> fixed) {
        ReadQuantities taken = within.fixing(fixed);
        return taken == within ? this : new ReadRegion(taken);
    }

    @Override
    public NumericDomain.Bounds runsBetween(NumericDomain.LinearForm<NumericTerm> form) {
        return within.runsBetween(form);
    }

    @Override
    public Optional<EmptyInput> emptiness() {
        return within.emptiness();
    }
}
