package souther.compiler.examples;

import souther.compiler.evaluate.DepthLimitExceeded;
import souther.compiler.evaluate.EvaluationContext;
import souther.compiler.evaluate.StepLimitExceeded;
import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.observe.Figure;
import souther.compiler.observe.WorkFigure;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Optional;
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

    /**
     * Which figure of {@code policy} a run that {@link #reached} its limits went past, at the
     * number {@code policy} held it to: its steps, or how deep it called. None where what ran out
     * was the host's stack, which no figure here was compared against, and none where the run was
     * abandoned — what gave up on it is what names its figure.
     */
    static Optional<Figure> figureOf(Throwable thrown, EvaluationPolicy policy) {
        return switch (EvaluationContext.overspent(thrown)) {
            case StepLimitExceeded _ ->
                    Optional.of(WorkFigure.EVALUATION_STEPS.at(policy.stepLimit()));
            case DepthLimitExceeded _ ->
                    Optional.of(WorkFigure.RECURSION_DEPTH.at(policy.recursionDepthLimit()));
            case null, default -> Optional.empty();
        };
    }

    private RunLimits() {}
}
