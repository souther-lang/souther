package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;

import java.util.IdentityHashMap;
import java.util.Map;

/**
 * Where each node of an expression stands in the order a run works the expression out: the nodes a
 * run always evaluates whenever it evaluates the expression, each with the stretch of the order
 * its own operands and it take up ({@link Evaluated#inOrder}). A node a run reaches only on some
 * evaluations — an arm, a right operand a left may settle, a function value — has no place, and
 * nothing is said of what comes before or after it.
 *
 * <p>The one order the places a run may stop in are put in: an operation of whole numbers and a
 * quotient are both read at a node, and which of two comes first is asked here and of nothing
 * else. A node comes after another where the stretch it takes up begins past where the other's
 * ends, so that nothing it works out is worked out before anything of the other.
 */
final class EvaluationPlaces {

    /** A node's stretch of the order: the first place of what it works out, and its own. */
    private record Stretch(int first, int own) {}

    private static final EvaluationPlaces NONE = new EvaluationPlaces(new IdentityHashMap<>());

    private final Map<Core, Stretch> stretches;

    private EvaluationPlaces(Map<Core, Stretch> stretches) {
        this.stretches = stretches;
    }

    /** No node has a place. */
    static EvaluationPlaces none() {
        return NONE;
    }

    /** The places of the nodes evaluating {@code expression} always works out. */
    static EvaluationPlaces of(Core expression) {
        Map<Core, Stretch> out = new IdentityHashMap<>();
        place(expression, out, new int[1]);
        return new EvaluationPlaces(out);
    }

    private static void place(Core expression, Map<Core, Stretch> out, int[] next) {
        Core node = Core.withoutStanding(expression);
        int first = next[0];
        for (Evaluated.Step step : Evaluated.inOrder(node)) {
            if (step instanceof Evaluated.Step.Always(Core part)) {
                place(part, out, next);
            }
        }
        out.put(node, new Stretch(first, next[0]++));
    }

    /**
     * Whether nothing {@code later} works out is worked out before everything {@code earlier}
     * does: both have a place, and the one begins past where the other ends. So an operation of
     * {@code later}, which may stop at any step of what it works out, stops after any stop of
     * {@code earlier}. False where either has none, which says no more than that it is not
     * known.
     */
    boolean comesAfter(Core later, Core earlier) {
        if (later == null || earlier == null) {
            return false;
        }
        Stretch after = stretches.get(Core.withoutStanding(later));
        Stretch before = stretches.get(Core.withoutStanding(earlier));
        return after != null && before != null && after.first() > before.own();
    }
}
