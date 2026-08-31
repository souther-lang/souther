package souther.compiler.check;

import souther.compiler.ast.Hir;

import java.util.Optional;

/**
 * A clause the language reads as a comparison: its two sides, and what its operator placed.
 *
 * <p>What {@link Comparison} is for a checked body's binary, for a clause read off the syntax tree.
 * The two recognitions are separate because what they read a comparison out of is: a rule of a
 * {@code data} is read before anything has been checked, and a body's comparison is a
 * {@code Core.Binary}. What they share is the claim, which is what the operator placed and is the
 * same answer wherever the comparison was written.
 *
 * <p><b>No operator here.</b> The claim is the meaning of the one this was recognised from, and a
 * reader handed both could turn the claim round and go on holding an operator that states the
 * comparison the other way about. What such a reader answers from the operator is not what the
 * value says, and nothing tells the two apart. So the operator goes no further than {@link #of},
 * and what a reader wanting the sides the other way round asks for is {@link #turned}.
 */
final class ClauseComparison {

    private final Hir.Expr left;
    private final Hir.Expr right;
    private final ComparisonClaim claim;

    private ClauseComparison(Hir.Expr left, Hir.Expr right, ComparisonClaim claim) {
        this.left = left;
        this.right = right;
        this.claim = claim;
    }

    /** {@code clause} as a comparison, or nothing where it is not one or its operator compares no
     *  values. */
    static Optional<ClauseComparison> of(Hir.Expr clause) {
        if (!(clause instanceof Hir.Binary bin)) {
            return Optional.empty();
        }
        return switch (ComparisonPlacement.of(bin.op())) {
            case ComparisonPlacement.Nothing _ -> Optional.empty();
            case ComparisonClaim claim ->
                    Optional.of(new ClauseComparison(bin.left(), bin.right(), claim));
        };
    }

    /**
     * The same comparison with its sides the other way round, which is what a reader wanting the
     * side it is reading for on the left asks for.
     *
     * <p>The sides and the claim move together, because {@code 0 <= value} states of the value what
     * {@code value >= 0} states. Swapped by a caller and left to turn the claim itself, the two go
     * out of step at whichever caller forgets, and what it then reads is the comparison the source
     * did not write.
     */
    ClauseComparison turned() {
        return new ClauseComparison(right, left, claim.turned());
    }

    /** The side the claim is stated of. */
    Hir.Expr left() {
        return left;
    }

    /** What that side is compared against. */
    Hir.Expr right() {
        return right;
    }

    /** What the comparison placed on the values of its left side. */
    ComparisonClaim claim() {
        return claim;
    }
}
