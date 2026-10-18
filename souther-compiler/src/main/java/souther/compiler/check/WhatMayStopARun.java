package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

/**
 * Whether working an expression out may answer nothing on some rows, as far as a reading of what
 * it states would say so: it divides by something other than a number written, which divides by
 * nought where that something is nought, or it hands something to a helper, a behavior or a
 * function value, whose body is not in this tree and may.
 *
 * <p>Read off what the tree writes and kept on the side of saying it may. What it is for is
 * telling where a reading has to say which of several applications a run reaches, and saying that
 * of one that never stops costs a reading and nothing more.
 */
public final class WhatMayStopARun {

    private WhatMayStopARun() {
    }

    /** Whether working {@code e} out may answer nothing on some rows. */
    public static boolean in(Core e) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.Binary binary && binary.op() == BinOp.DIV
                && !(Core.withoutStanding(binary.right()) instanceof Core.Int
                        || Core.withoutStanding(binary.right()) instanceof Core.Decimal)) {
            return true;
        }
        if (node instanceof Core.Apply) {
            return true;
        }
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied != null && !(applied.operation() instanceof ValueName.Stdlib)) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(node, child -> found[0] = found[0] || in(child));
        return found[0];
    }
}
