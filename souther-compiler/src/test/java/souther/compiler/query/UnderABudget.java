package souther.compiler.query;

import souther.compiler.partition.AdequacyPolicy;

/**
 * A compilation held to a budget of the test's choosing, for a test that lives beside the code it
 * exercises rather than beside the compilation.
 *
 * <p>Setting the budget is the compilation's own and not something a build reaches, so the setter
 * is not public. What this hands over is only that setter, for a test in another package that wants
 * a small limit in order to reach, with a small model, what a large one reaches under the standard
 * budget.
 */
public final class UnderABudget {

    private UnderABudget() {}

    public static Compilation of(Compilation compilation, AdequacyPolicy policy) {
        return compilation.withAdequacyPolicy(policy);
    }
}
