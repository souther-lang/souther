package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;

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

    /**
     * The places of the nodes evaluating {@code expression} always works out, of those it holds
     * at one place and no more. What is said of a node is said of every place it is worked out
     * at, so it is said only of a node the whole of the expression holds once: a node held at
     * two places has two, and so have the nodes under it, and none of them has a place that
     * could be said.
     */
    static EvaluationPlaces of(Core expression) {
        Map<Core, Stretch> out = new IdentityHashMap<>();
        place(expression, out, heldAtMoreThanOnePlace(expression), new int[1]);
        return new EvaluationPlaces(out);
    }

    /** Every node {@code root} holds at more than one place of its structure, wherever a run
     *  works them out, and everything under such a node. Each node is walked once. */
    private static Set<Core> heldAtMoreThanOnePlace(Core root) {
        Set<Core> met = Collections.newSetFromMap(new IdentityHashMap<>());
        Set<Core> shared = Collections.newSetFromMap(new IdentityHashMap<>());
        meet(root, met, shared);
        Set<Core> marked = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Core each : List.copyOf(shared)) {
            markEverythingUnder(each, marked, shared);
        }
        return shared;
    }

    private static void meet(Core expression, Set<Core> met, Set<Core> shared) {
        Core node = Core.withoutStanding(expression);
        if (met.add(node)) {
            Core.forEachChild(node, child -> meet(child, met, shared));
        } else {
            shared.add(node);
        }
    }

    private static void markEverythingUnder(Core expression, Set<Core> marked, Set<Core> shared) {
        Core node = Core.withoutStanding(expression);
        if (marked.add(node)) {
            shared.add(node);
            Core.forEachChild(node, child -> markEverythingUnder(child, marked, shared));
        }
    }

    /** Puts {@code expression} and what it always works out in the order, but for what is
     *  {@code shared}. */
    private static void place(Core expression, Map<Core, Stretch> out, Set<Core> shared,
                              int[] next) {
        Core node = Core.withoutStanding(expression);
        if (shared.contains(node)) {
            return;
        }
        int first = next[0];
        for (Evaluated.Step step : Evaluated.inOrder(node)) {
            if (step instanceof Evaluated.Step.Always(Core part)) {
                place(part, out, shared, next);
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

    /**
     * Whether {@code later} itself is worked out after everything {@code earlier} works out: both
     * have a place, and its own is past where the other's ends. So what stops at {@code later}'s
     * own step — a quotient, at its divisor — stops after any stop of {@code earlier}, though what
     * {@code later} works out on its way to it, such as its operands, may come first. False where
     * either has none.
     */
    boolean isWorkedOutAfter(Core later, Core earlier) {
        if (later == null || earlier == null) {
            return false;
        }
        Stretch after = stretches.get(Core.withoutStanding(later));
        Stretch before = stretches.get(Core.withoutStanding(earlier));
        return after != null && before != null && after.own() > before.own();
    }

    /** Whether {@code node} has a place in the order. */
    boolean hasAPlace(Core node) {
        return node != null && stretches.containsKey(Core.withoutStanding(node));
    }

    /**
     * Whether {@code holds} is true of every node of {@code root}'s tree that a run may work out
     * before it takes the step {@code site} stands for: the one walk over what a run stopping at
     * {@code site} has got past.
     *
     * <p>A node whose stretch of the order begins past {@code site} is worked out after it
     * ({@link #comesAfter}), and so is everything under it, a branch or an arm included: none of it
     * is asked. A node whose own step comes after {@code site}'s ({@link #isWorkedOutAfter}) is not
     * asked of itself, but what it is made of may come before and is walked. Where {@code site} is
     * in the stretch of a node, it is in what the node always works out, and what the node enters
     * only after that — an arm, the right of an operator that may settle, a body — is worked out
     * after {@code site} though it has no place: only what the node always works out is walked.
     * Everything else that has no place may come before, and is asked: what is not known is not
     * taken to be after.
     */
    boolean everyNodeNotAfter(Core root, Core site, Predicate<Core> holds) {
        return everyNodeNotAfter(root, site, holds,
                Collections.newSetFromMap(new IdentityHashMap<>()));
    }

    private boolean everyNodeNotAfter(Core expression, Core site, Predicate<Core> holds,
                                      Set<Core> met) {
        Core node = Core.withoutStanding(expression);
        if (!met.add(node) || comesAfter(node, site)) {
            return true;
        }
        if (!isWorkedOutAfter(node, site) && !holds.test(node)) {
            return false;
        }
        boolean[] every = {true};
        Consumer<Core> walk = child -> {
            if (every[0]) {
                every[0] = everyNodeNotAfter(child, site, holds, met);
            }
        };
        if (holdsTheSite(node, site)) {
            for (Evaluated.Step step : Evaluated.inOrder(node)) {
                if (step instanceof Evaluated.Step.Always(Core part)) {
                    walk.accept(part);
                }
            }
        } else {
            Core.forEachChild(node, walk);
        }
        return every[0];
    }

    /** Whether {@code site} stands in what {@code node} always works out: both have a place, and
     *  the site's step is taken within the stretch of the node and before the node's own. */
    private boolean holdsTheSite(Core node, Core site) {
        if (site == null) {
            return false;
        }
        Stretch around = stretches.get(Core.withoutStanding(node));
        Stretch at = stretches.get(Core.withoutStanding(site));
        return around != null && at != null && around.first() <= at.own()
                && at.own() < around.own();
    }
}
