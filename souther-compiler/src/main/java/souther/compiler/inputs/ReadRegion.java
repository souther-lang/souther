package souther.compiler.inputs;

import souther.compiler.check.HeldClass;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleRef;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;
import souther.compiler.values.ValueSet;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

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
    public SearchRegion leavingOut(Set<PartId<RuleRef.Invariant>> parts) {
        return parts.isEmpty() ? this : new ReadRegion(within.leavingOut(parts));
    }

    @Override
    public Assumption assuming(LinearForm<NumericTerm> form,
                               Rel rel) {
        return switch (within.assuming(form, rel)) {
            // The same region where the rules came back as they were, which is a constraint they
            // already held. A region that took it in is what this says, and it says nothing about
            // whether anything moved.
            case ReadQuantities.Taking.Taken(ReadQuantities taken) -> new Assumption.Taken(
                    taken == within ? this : new ReadRegion(taken));
            case ReadQuantities.Taking.Refused(Refusal why) -> new Assumption.Refused(why);
        };
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
    public PlacesApart apartAt(NumericTerm.FromOnePosition term) {
        return within.apartAt(term);
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
    public NumericDomain.FormProjection projectionOf(NumericTerm term,
                                                     Collection<? extends NumericTerm> alongside) {
        return within.projectionOf(term, alongside);
    }

    @Override
    public NumericDomain.Bounds wholeRunOf(NumericTerm.FromOnePosition term) {
        if (!apartAt(term).isEmpty()
                || (term instanceof NumericTerm.ValueOf value
                        && !(classAt(value) instanceof HeldClass.None))) {
            return null;
        }
        return within.wholeRunOf(term);
    }

    @Override
    public HeldClass classAt(NumericTerm.ValueOf place) {
        return within.classAt(place);
    }

    @Override
    public ValueSet admittedAt(NumericTerm.FromOnePosition term) {
        return within.admittedAt(term);
    }

    @Override
    public ValueSet heldAt(NumericTerm.FromOnePosition term) {
        return within.heldAt(term);
    }

    @Override
    public ReadingsOfEachValue readingsOfEach(List<NumericTerm.FromOnePosition> terms) {
        return within.readingsOfEach(terms);
    }

    @Override
    public Optional<EmptyInput> emptiness() {
        return within.emptiness();
    }
}
