package souther.compiler.inputs;

import souther.compiler.check.HeldClass;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleRef;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedRuns;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.ValueName;
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
    public NarrowingsKept narrowingsKept() {
        return within.narrowingsKept();
    }

    @Override
    public SearchRegion withoutTheRelationOf(Map<String, Set<PartId<RuleRef.Invariant>>> parts) {
        return parts.isEmpty() ? this : new ReadRegion(within.withoutTheRelationOf(parts));
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
    public OrderedRuns orderedRegionAt(NumericTerm.ValueOf place) {
        return within.orderedRegionAt(place);
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
    public boolean emptinessIsSettled() {
        return within.emptinessIsSettled();
    }

    /**
     * A region of numbers read from rules and taken in or fixed on top of them: the run of a
     * position is where the closure of everything said leaves it, and the closure of more said
     * leaves it no wider. A class is the declarations' narrowed by the remainders pinned, and never
     * widened.
     *
     * <p>For regions that are not shown empty, and held, not derived: over the regions a model
     * reads — numbers of several classes, the cases of a sum, the elements and the size of a list,
     * a remainder — with a number fixed, a relation taken in, one number taken against a value, or
     * one held apart from a value, each said at random
     * ({@code ARegionRunsNoWiderOnceMoreIsSaidTest}).
     *
     * <p>So only for the numbers that test makes: the value a position holds, a floor remainder of
     * one, and the length of a list. What else is taken of a position — the sum of a list, a
     * quotient, the parts of a date or a time, the length of a string, the size of a set — is a
     * number it has not been held for, and a region asked about one of those says no.
     */
    @Override
    public boolean runsOnlyNarrowWhenFixed(Collection<? extends NumericTerm> terms) {
        return terms.stream().allMatch(ReadRegion::heldFor);
    }

    private static final ValueName.Stdlib LIST_LENGTH = ValueName.Stdlib.operation("List", "length");

    /** Whether {@link #runsOnlyNarrowWhenFixed} has been held for this kind of number. */
    private static boolean heldFor(NumericTerm term) {
        if (term instanceof NumericTerm.ValueOf) {
            return true;
        }
        if (!(term instanceof NumericTerm.TakenOf taken)) {
            return false;
        }
        return taken.takenAs() instanceof TakenAs.TheFloorRemainder
                || (taken.takenAs() instanceof TakenAs.HowManyItHolds
                        && LIST_LENGTH.equals(taken.operation()));
    }

    @Override
    public Optional<EmptyInput> emptiness() {
        return within.emptiness();
    }
}
