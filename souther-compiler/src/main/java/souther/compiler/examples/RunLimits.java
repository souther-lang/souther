package souther.compiler.examples;

import souther.compiler.evaluate.EvaluationContext;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;

/**
 * Whether a run went past what a run may spend, read off what stopped it.
 *
 * <p>One question asked in one place. A run that ran out says nothing about the program — given more
 * it might have answered — and a run that stopped of its own accord does: two readers deciding which
 * of the two they were handed apart is how a run out of budget came to be read as a run that answered
 * differently.
 */
final class RunLimits {

    /**
     * Whether {@code thrown} is, or carries, a run going past its steps, its depth or its stack.
     * What it is wrapped in is looked through, since what the applied code ends with arrives as a
     * failure of the call that ran it.
     */
    static boolean reached(Throwable thrown) {
        if (EvaluationContext.overspent(thrown) != null) {
            return true;
        }
        Set<Throwable> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Throwable each = thrown; each != null && seen.add(each); each = each.getCause()) {
            if (each instanceof StackOverflowError || each instanceof StackExhaustedException) {
                return true;
            }
        }
        return false;
    }

    private RunLimits() {}
}
