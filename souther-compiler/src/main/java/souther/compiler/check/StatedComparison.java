package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.NumericDomain.Rel;

/**
 * A comparison a reading arrived at: what it places, and the two values it places it on.
 *
 * <p>What every reader of a condition wants and all it wants. A relation is stated of two sides, and
 * which relation it is comes from what the comparison placed ({@link ComparisonClaim}) — so a reader
 * handed one of these has the whole of what a comparison says without going back to an operator.
 *
 * <p><b>Beside {@link Comparison} and not the same thing.</b> That one is a binary the source wrote,
 * recognised where it stands, and what it carries besides the claim is the node — which is what a
 * reader asking where a comparison is in the tree wants ({@link
 * souther.compiler.coverage.ComparisonCatalog}). This one is a statement, and a statement has no
 * place in the tree: a reading that works out what an operation answering an order proves about its
 * two arguments states a comparison no author wrote, and there is nowhere it stands.
 *
 * <p><b>And it carries no site.</b> A comparison is filed under what it places and the terms its two
 * sides are ({@link Terms}), so where a comparison came from, what it answers and where it stands
 * decide nothing a reader of this asks. Carrying them would leave one field whose only use is
 * putting the node back together, and putting the node back together is what a statement exists
 * instead of. Whoever reports about a clause holds the expression the source wrote and reports about
 * that.
 */
record StatedComparison(ComparisonClaim claim, Core left, Core right) {

    /**
     * The relation this states, asserted with polarity {@code positive}.
     *
     * <p>Asserted false, what a comparison states is what holds where it does not — which is the
     * claim's own answer ({@link ComparisonClaim#denied}) and not a table of six turned round here.
     * Written once because every reader of a condition asks it under a polarity, and two of them
     * pairing the denial with the relation themselves are two places that can come to pair it
     * differently.
     */
    Rel relationUnder(boolean positive) {
        return (positive ? claim : claim.denied()).statedRelation();
    }
}
