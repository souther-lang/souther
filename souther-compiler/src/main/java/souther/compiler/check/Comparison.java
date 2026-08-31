package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.Optional;

/**
 * A binary the language reads as a comparison, together with what its operator placed.
 *
 * <p><b>The two are one value because they have to agree.</b> What a rule places is a function of
 * the operator it was written with, and every reader below the point where a node was recognised as
 * a comparison needs both: the node to read the two sides from, and the claim to say what the rule
 * states about the line. Passed as two arguments, the pair is only as true as each caller made it;
 * held here, there is nowhere for a claim of one operator to arrive beside the node of another.
 *
 * <p><b>Made in one place, which is what carries the recognition.</b> {@link #of} is the only way
 * in, so a value of this type is itself the evidence that the operator compares — a reader holding
 * one has no case left for an operator that placed nothing, and no reason to go back to the operator
 * and ask again. A {@code boolean} answering the same question leaves the fact behind at the
 * {@code if}, which is how the readings below came to carry the wider classification and answer for
 * a case none of them could be handed.
 *
 * <p><b>Equal where the nodes are equal.</b> The claim is read off the node's operator, so it adds
 * nothing to tell two of these apart, and a record holding one compares as it did when it held the
 * node alone. This is a comparison's value and not an occurrence's identity: which occurrence of a
 * comparison a body is at is a question about the tree, kept where the tree is
 * ({@link souther.compiler.coverage.ComparisonCatalog}), and a reader wanting that asks about the
 * node.
 */
public final class Comparison {

    private final Core.Binary at;
    private final ComparisonClaim claim;

    private Comparison(Core.Binary at, ComparisonClaim claim) {
        this.at = at;
        this.claim = claim;
    }

    /** {@code at} as a comparison, or nothing where its operator compares no values. */
    public static Optional<Comparison> of(Core.Binary at) {
        return switch (ComparisonPlacement.of(at.op())) {
            case ComparisonPlacement.Nothing _ -> Optional.empty();
            case ComparisonClaim claim -> Optional.of(new Comparison(at, claim));
        };
    }

    /** The comparison itself, for a reader of what its two sides name. */
    public Core.Binary at() {
        return at;
    }

    /** What its operator placed on the values. */
    public ComparisonClaim claim() {
        return claim;
    }

    /** Everything this holds, which is what an identity is of. The claim adds nothing to the
     *  answer — it is read off the node's operator, so two of these over one node carry one claim —
     *  and it is read here all the same, because a field left out of an identity is a field a
     *  reader of the identity is told has not changed. */
    @Override
    public boolean equals(Object other) {
        return other instanceof Comparison that
                && at.equals(that.at) && claim.equals(that.claim);
    }

    /** Off the node alone, which spreads these exactly as the claim would: one node has one
     *  claim. */
    @Override
    public int hashCode() {
        return at.hashCode();
    }

    @Override
    public String toString() {
        return "Comparison[" + at + "]";
    }
}
