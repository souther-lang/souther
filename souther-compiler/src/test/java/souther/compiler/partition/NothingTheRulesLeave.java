package souther.compiler.partition;

import souther.compiler.check.Emptiness;
import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.Optional;

/**
 * A region shown to hold nothing, for tests about what a search does when it is handed one.
 *
 * <p>Beside {@link NothingTheRulesSay} and the opposite of it. That one narrows nothing and this one
 * leaves nothing, and both answer every question about where a form runs with neither end — which
 * is the pair a reader has to tell apart by asking rather than by reading the ends.
 */
final class NothingTheRulesLeave implements SearchRegion {

    static final SearchRegion REGION = new NothingTheRulesLeave();

    @Override
    public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
        return new Assumption.Taken(this);
    }

    @Override
    public SearchRegion assuming(NumericTerm.FromOnePosition term,
                                 souther.compiler.numeric.Place at, Rel rel) {
        return this;
    }

    @Override
    public SearchRegion given(Map<NumericTerm, souther.compiler.numeric.Place> fixed) {
        return this;
    }

    @Override
    public SearchRegion apartFrom(NumericTerm.FromOnePosition term,
                                  souther.compiler.numeric.Place at) {
        return this;
    }

    /**
     * Nowhere for anything to run, said as what it is.
     *
     * <p>What a reader that went on to read ends would get is the widest range there is, which is
     * the thing being guarded against — so a search reaching here at all is a search that did not
     * ask whether there was anything to look in.
     */
    @Override
    public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
        return new NumericDomain.FormProjection.NothingIsLeft();
    }

    @Override
    public Optional<EmptyInput> emptiness() {
        return Optional.of(new EmptyInput.ProvedByTheRules(new Emptiness.ConflictingRules()));
    }

    private NothingTheRulesLeave() {}
}
