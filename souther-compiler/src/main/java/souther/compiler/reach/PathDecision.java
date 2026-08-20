package souther.compiler.reach;

import souther.compiler.diag.SourcePos;

/**
 * One condition on the way to a place, and the way it went.
 *
 * <p>Collected where the assumption is made and not worked out afterwards from where the place
 * sits. A reading that rebuilt this from the tree would be a second account of what was assumed,
 * and the one that matters is the one the domains were actually given — a condition of a shape
 * nothing could take in is not on this list, and a proof naming it would be claiming it did work
 * it did not do.
 *
 * @param at   where the condition is written
 * @param held whether the way here was the way the condition holds
 */
public record PathDecision(SourcePos at, boolean held) {

    public PathDecision {
        if (at == null) {
            throw new IllegalArgumentException("a condition written nowhere decided nothing");
        }
    }
}
