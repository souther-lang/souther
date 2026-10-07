package souther.compiler.partition;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The order the parameters of one row are composed in, and which parameters' values each of them
 * turns on.
 *
 * <p>One answer for every walk that composes a row parameter by parameter. A container handed the
 * value at another parameter is composed after that parameter, and what came of composing it turns
 * on that parameter's value — and on every value that one's turned on in turn: a box holding the
 * number, and an outer list holding the box, is an outer list another number may let be built.
 * Worked out once here, the order, whether a parameter has to wait for one after it, and whether
 * one coming to nothing is a reason to try another value of an earlier one are one reading; a walk
 * that answered any of them itself would answer it its own way.
 *
 * @param parameters the parameters, in the order they are declared
 * @param order      their declared positions in the order they are composed
 * @param turnsOn    for each parameter, every parameter whose value reaches one of its
 *                   containers, through as many containers as it takes
 */
record CompositionOrder(List<String> parameters, List<Integer> order,
                        Map<String, Set<String>> turnsOn) {

    CompositionOrder {
        parameters = List.copyOf(parameters);
        order = List.copyOf(order);
        Map<String, Set<String>> copied = new LinkedHashMap<>();
        turnsOn.forEach((parameter, on) -> copied.put(parameter, Set.copyOf(on)));
        turnsOn = Map.copyOf(copied);
    }

    /** What ordering the parameters came to. */
    sealed interface Result {

        /** An order every container is composed after the values it is handed. */
        record Ordered(CompositionOrder order) implements Result {}

        /**
         * Parameters each of which is to hold a value of another of them, so none of them can be
         * composed first.
         *
         * <p>A fact about this walk and not about the model: the values could be chosen together,
         * and a walk that does would compose these. Kept as the parameters they are, so that one can.
         *
         * @param parameters in the order they are declared, which is the order a report names them
         *                   in
         */
        record Circular(List<String> parameters) implements Result {

            public Circular {
                parameters = List.copyOf(parameters);
            }
        }
    }

    /**
     * The order {@code parameters} are composed in under what {@code contents} asks: each after
     * every parameter whose value one of its containers is handed, and otherwise in the order they
     * are declared.
     */
    static Result of(List<String> parameters, ContentsAsked contents) {
        Map<String, Set<String>> after = new LinkedHashMap<>();
        contents.composedAfter().forEach((parameter, values) -> {
            if (parameters.contains(parameter)) {
                Set<String> among = new LinkedHashSet<>(values);
                among.retainAll(parameters);
                after.put(parameter, among);
            }
        });
        List<Integer> out = new ArrayList<>();
        Set<String> placed = new LinkedHashSet<>();
        while (out.size() < parameters.size()) {
            int next = -1;
            for (int p = 0; p < parameters.size() && next < 0; p++) {
                String head = parameters.get(p);
                if (!placed.contains(head)
                        && placed.containsAll(after.getOrDefault(head, Set.of()))) {
                    next = p;
                }
            }
            if (next < 0) {
                return new Result.Circular(parameters.stream()
                        .filter(each -> !placed.contains(each)).toList());
            }
            out.add(next);
            placed.add(parameters.get(next));
        }
        Map<String, Set<String>> reached = new LinkedHashMap<>();
        for (String parameter : parameters) {
            reached.put(parameter, reachedFrom(parameter, after));
        }
        return new Result.Ordered(new CompositionOrder(parameters, out, reached));
    }

    /** Every parameter whose value reaches {@code parameter}'s containers, directly or not. */
    private static Set<String> reachedFrom(String parameter, Map<String, Set<String>> after) {
        Set<String> out = new LinkedHashSet<>();
        Deque<String> left = new ArrayDeque<>(after.getOrDefault(parameter, Set.of()));
        while (!left.isEmpty()) {
            String each = left.pop();
            if (out.add(each)) {
                left.addAll(after.getOrDefault(each, Set.of()));
            }
        }
        return out;
    }

    /** The parameters whose values what came of the parameter at {@code p} turns on. */
    Set<String> turnsOn(int p) {
        return turnsOn.getOrDefault(parameters.get(p), Set.of());
    }

    /**
     * Whether what came of the parameter at {@code p} is about its own classes alone: whether no
     * other parameter's value reaches its containers.
     */
    boolean alone(int p) {
        return turnsOn(p).isEmpty();
    }

    /**
     * Whether the parameter at {@code failed} coming to nothing may come to something with
     * another value of the parameter at {@code p} — where that value reaches its containers.
     */
    boolean mayTurnOn(int failed, int p) {
        return turnsOn(failed).contains(parameters.get(p));
    }

    /**
     * Whether a parameter composed after the {@code next}-th in the order turns on the value of the
     * one composed there — which is what makes a value of it one to hand on and wait for, rather
     * than the first one composed.
     */
    boolean awaited(int next) {
        for (int later : order.subList(next + 1, order.size())) {
            if (mayTurnOn(later, order.get(next))) {
                return true;
            }
        }
        return false;
    }
}
