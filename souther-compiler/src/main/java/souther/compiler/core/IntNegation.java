package souther.compiler.core;

import souther.compiler.ast.Hir;

/**
 * Where negating an {@code Int} has a value.
 *
 * <p>The smallest {@code Int} has no positive counterpart, so its negation is what the run time
 * aborts on and names no number (spec §stdlib-int). Every reader that reads a written negation as
 * a number asks here, so that none of them decides for itself and reads {@code +2^63} where the
 * run time reads nothing.
 */
public final class IntNegation {

    private IntNegation() {}

    /** Whether {@code -operand} is an {@code Int}. */
    public static boolean hasValue(long operand) {
        return operand != Long.MIN_VALUE;
    }

    /** Whether {@code operand}, a negation's own, is the smallest {@code Int} written out: the
     *  negation it stands under has no value. */
    public static boolean isTheLeastInt(Hir.Expr operand) {
        return operand instanceof Hir.IntLit i && !hasValue(i.value());
    }

    /** As {@link #isTheLeastInt(Hir.Expr)}, for the checked form. */
    public static boolean isTheLeastInt(Core operand) {
        return Core.withoutStanding(operand) instanceof Core.Int i && !hasValue(i.value());
    }
}
