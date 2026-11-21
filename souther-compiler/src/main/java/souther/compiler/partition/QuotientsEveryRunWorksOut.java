package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSites;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;

import java.util.ArrayList;
import java.util.List;

/**
 * The quotients a run works out whenever it evaluates an expression, in the order it works them
 * out: each one that stops the run where its divisor is nought ({@link AbortKind#DIVISION_BY_ZERO},
 * as {@link AbortSites} says of the operator).
 *
 * <p>Read off the evaluation order of the expression ({@link Evaluated}) and nothing else, so that
 * a quotient is here only where evaluating the expression reaches it, and one quotient is before
 * another only where the run works it out first. A quotient in an arm, behind the left of a
 * condition that settles its answer, or in a function value, is entered by some evaluations and not
 * by others, and is not here.
 */
final class QuotientsEveryRunWorksOut {

    private QuotientsEveryRunWorksOut() {}

    /** The quotients evaluating {@code expression} always works out, the first worked out first. */
    static List<Core.Binary> in(Core expression) {
        List<Core.Binary> out = new ArrayList<>();
        collect(expression, out);
        return List.copyOf(out);
    }

    private static void collect(Core expression, List<Core.Binary> out) {
        Core node = Core.withoutStanding(expression);
        for (Evaluated.Step step : Evaluated.inOrder(node)) {
            if (step instanceof Evaluated.Step.Always(Core part)) {
                collect(part, out);
            }
        }
        if (node instanceof Core.Binary binary
                && AbortSites.ofAnOperator(binary).contains(AbortKind.DIVISION_BY_ZERO)) {
            out.add(binary);
        }
    }
}
