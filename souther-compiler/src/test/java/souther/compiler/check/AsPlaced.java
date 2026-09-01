package souther.compiler.check;

import souther.compiler.types.BinOp;

/**
 * What an operator placed, for a test that names the operator rather than a node.
 *
 * <p>{@link Comparison} is how a reader comes by a claim, and it wants a node — so a test whose
 * subject is the operator itself has to narrow {@link ComparisonPlacement} instead. Here rather
 * than wherever such a test stands, because narrowing the wide answer in each of them is the shape
 * the readings below a recognition stopped having: one of them holding an operator that placed
 * nothing would answer for a case the test meant to exclude, and it would say so as a class cast
 * somewhere in the middle of what it was checking.
 */
final class AsPlaced {

    private AsPlaced() {
    }

    /** What {@code op} placed, where the test's own subject is that it places something. */
    static ComparisonClaim claim(BinOp op) {
        if (ComparisonPlacement.of(op) instanceof ComparisonClaim placed) {
            return placed;
        }
        throw new IllegalArgumentException("this places nothing, so there is no claim: " + op);
    }
}
