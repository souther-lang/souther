package souther.compiler.partition;

import souther.compiler.regex.PatternPlan;
import souther.compiler.values.ValueSet;

/**
 * A search whose declarations leave every position every value there is.
 *
 * <p>For a test whose subject is the region rather than the sets: the walk still has to be handed
 * both, and a set that narrows nothing is what leaves the region the only thing deciding where a
 * position may stand. Written per test instead, each would be one more place a set could quietly
 * take a candidate away and the test would read as though the region had.
 *
 * <p>The allowance is the one a witness is granted anywhere else, so what a crossing may cost here
 * is what it costs in a compilation.
 */
final class NothingTheDeclarationsNarrow {

    static final WitnessSearch LOOKING = new WitnessSearch(
            _ -> new AdmittedValues.Admitted.Values(ValueSet.ANY),
            PatternPlan.Budget.OF_A_WITNESS::meter);

    private NothingTheDeclarationsNarrow() {}
}
