package souther.compiler.partition;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;

import java.util.Map;
import java.util.Optional;

/**
 * A region the declarations narrow in no way, for tests about what a search does on its own.
 *
 * <p>Every value there is, and nothing proved empty. A test handing over a region that says
 * something is testing the region as well as the reader, and a reader that came back empty-handed
 * would leave which of the two answered unsaid.
 */
final class NothingTheRulesSay implements SearchRegion {

    static final SearchRegion REGION = new NothingTheRulesSay();

    @Override
    public SearchRegion assuming(NumericDomain.LinearForm<NumericTerm> form,
                                 NumericDomain.Rel rel) {
        return this;
    }

    @Override
    public SearchRegion given(Map<NumericTerm, Count> fixed) {
        return this;
    }

    @Override
    public NumericDomain.Bounds runsBetween(NumericDomain.LinearForm<NumericTerm> form) {
        return NumericDomain.Bounds.OPEN;
    }

    @Override
    public Optional<EmptyInput> emptiness() {
        return Optional.empty();
    }

    private NothingTheRulesSay() {}
}
