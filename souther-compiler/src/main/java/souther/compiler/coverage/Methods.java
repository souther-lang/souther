package souther.compiler.coverage;

import souther.compiler.ast.DefinitionName;
import souther.compiler.core.Core;
import souther.compiler.types.ReachName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * The methods of a module a run of one of its behaviors passes through, and which of them each
 * behavior reaches.
 *
 * <p>What a behavior emits is its own body and the body of every method it calls, directly or
 * through another. A value's method is one body with one set of probes however many behaviors call
 * it, so the places it holds are physically in it and are owed by each behavior that reaches it.
 * Which bodies those are is asked here and nowhere else: a reader that took a behavior's body alone
 * would be looking for a comparison in a body that does not hold it.
 *
 * <p>A helper emitted as a method is a body a run passes through as well, with no places counted.
 * It is a node of the graph all the same: a value's method called from inside it is reached by a
 * run that reaches the helper, and a graph of the counted bodies alone loses that method with it.
 *
 * <p>Which method a call runs is answered here too, and the closures are made of that answer. A
 * reader that goes into a method where a call runs it and a closure that says which methods a
 * behavior owes are one call graph read two ways; a reader deciding for itself which calls run a
 * method would be a second graph, agreeing with this one until a new kind of callee arrives.
 *
 * @param entries  each behavior's body, by the behavior's name
 * @param bodies   each value's method, by the name of the value
 * @param passages each helper's method, by the name of the helper
 * @param calls    the methods each body calls directly, behaviors, values and helpers alike, by
 *                 its name
 * @param calledBy the values' methods each behavior reaches, directly or through another method,
 *                 by the behavior's name
 */
record Methods(Map<String, Core> entries, Map<String, Core> bodies, Map<String, Core> passages,
               Map<String, Set<String>> calls, Map<String, Set<String>> calledBy) {

    /** A module with no method, which is what a hand-built plan holds. */
    static final Methods NONE = new Methods(Map.of(), Map.of(), Map.of(), Map.of(), Map.of());

    /** The methods of {@code module}, and which of its behaviors reach which. */
    static Methods of(ModuleBodies module) {
        Map<String, Core> methods = new LinkedHashMap<>(module.methods());
        methods.putAll(module.passages());
        Map<String, Set<String>> direct = new LinkedHashMap<>();
        module.bodies().forEach((name, body) -> direct.put(name, callsOf(body, methods)));
        methods.forEach((name, body) -> direct.put(name, callsOf(body, methods)));
        Map<String, Set<String>> reached = new LinkedHashMap<>();
        for (String behavior : module.bodies().keySet()) {
            Set<String> all = closure(direct.get(behavior), direct::get);
            all.retainAll(module.methods().keySet());
            reached.put(behavior, Collections.unmodifiableSet(all));
        }
        return new Methods(Collections.unmodifiableMap(new LinkedHashMap<>(module.bodies())),
                Map.copyOf(module.methods()), Map.copyOf(module.passages()), Map.copyOf(direct),
                Map.copyOf(reached));
    }

    /**
     * Whether {@code behavior} owes what the body named {@code body} holds: its own, and the
     * values' methods it reaches'.
     */
    boolean owes(String behavior, String body) {
        return body.equals(behavior) || calledBy.getOrDefault(behavior, Set.of()).contains(body);
    }

    /** The values' methods {@code emitted} reaches, directly or through another method, whichever
     *  behavior it is. */
    List<Core> calledFrom(Core emitted) {
        Map<String, Core> all = all();
        Set<String> reached = closure(callsOf(emitted, all), name -> callsOf(all.get(name), all));
        List<Core> out = new ArrayList<>();
        for (String name : reached) {
            if (bodies.containsKey(name)) {
                out.add(bodies.get(name));
            }
        }
        return out;
    }

    /**
     * The bodies a run of {@code behavior} goes through: its own, then each method it reaches, with
     * the methods a cycle of calls goes round kept together and every method that calls into them
     * from outside before them.
     *
     * <p>In that order because a reader carrying what holds where a call is made into the method it
     * runs has to have read every such call before it reads the method. A cycle has no such order
     * inside it, and needs none: a run at a call from one of its methods to another came into the
     * cycle from outside it first, so the ways into the cycle are the calls from outside.
     *
     * <p>Only helpers go round a cycle. A value that reaches itself — by naming a value, or calling a
     * helper that does — is refused before its body is made, so a cycle through a value's method is
     * this compiler's defect and is refused here, where the order is made.
     *
     * @param plan the plan these are the methods of, which the run is read against
     */
    RunBodies run(String behavior, CoverageSites.Plan plan) {
        Cycles found = new Cycles();
        for (String callee : calls.getOrDefault(behavior, Set.of())) {
            found.visit(callee);
        }
        Map<String, Core> all = all();
        List<List<Core>> groups = new ArrayList<>();
        for (List<String> cycle : found.finished.reversed()) {
            boolean round = cycle.size() > 1
                    || calls.get(cycle.getFirst()).contains(cycle.getFirst());
            List<Core> group = new ArrayList<>();
            for (String name : cycle) {
                if (round && bodies.containsKey(name)) {
                    throw new IllegalStateException("the method of `" + name + "` is on a cycle of"
                            + " calls " + cycle + ", and a value that reaches itself is refused"
                            + " before its body is made");
                }
                group.add(all.get(name));
            }
            groups.add(group);
        }
        return new RunBodies(entries.get(behavior), groups, this, plan);
    }

    /**
     * The strongly connected parts of the calls under some behavior, each finished after every
     * part it calls into — so reversed, every part is after the parts that call into it.
     */
    private final class Cycles {

        private final Map<String, Integer> index = new HashMap<>();
        private final Map<String, Integer> low = new HashMap<>();
        private final Deque<String> stack = new ArrayDeque<>();
        private final Set<String> onStack = new LinkedHashSet<>();
        private final List<List<String>> finished = new ArrayList<>();

        void visit(String name) {
            if (index.containsKey(name)) {
                return;
            }
            index.put(name, index.size());
            low.put(name, index.get(name));
            stack.push(name);
            onStack.add(name);
            for (String callee : calls.get(name)) {
                if (!index.containsKey(callee)) {
                    visit(callee);
                    low.put(name, Math.min(low.get(name), low.get(callee)));
                } else if (onStack.contains(callee)) {
                    low.put(name, Math.min(low.get(name), index.get(callee)));
                }
            }
            if (low.get(name).equals(index.get(name))) {
                List<String> cycle = new ArrayList<>();
                String member;
                do {
                    member = stack.pop();
                    onStack.remove(member);
                    cycle.add(member);
                } while (!member.equals(name));
                finished.add(cycle.reversed());
            }
        }
    }

    /** The name of the method of this module {@code call} runs, or null where it runs none. */
    String methodOf(Core.Call call) {
        return methodOf(call, name -> bodies.containsKey(name) || passages.containsKey(name));
    }

    /** Every method a run may pass through, values' and helpers', by name. */
    Map<String, Core> all() {
        Map<String, Core> all = new HashMap<>(bodies);
        all.putAll(passages);
        return all;
    }

    /** Every name reached from {@code start} along {@code next}, in the order first reached. */
    private static Set<String> closure(Set<String> start, Function<String, Set<String>> next) {
        Set<String> all = new LinkedHashSet<>();
        Deque<String> pending = new ArrayDeque<>(start);
        while (!pending.isEmpty()) {
            String name = pending.removeFirst();
            if (all.add(name)) {
                pending.addAll(next.apply(name));
            }
        }
        return all;
    }

    /** The methods among {@code methods} that {@code body} calls. */
    private static Set<String> callsOf(Core body, Map<String, Core> methods) {
        Set<String> out = new LinkedHashSet<>();
        collectCalls(body, methods, out);
        return out;
    }

    private static void collectCalls(Core e, Map<String, Core> methods, Set<String> out) {
        if (e == null) {
            return;
        }
        if (e instanceof Core.Call call) {
            String called = methodOf(call, methods::containsKey);
            if (called != null) {
                out.add(called);
            }
        }
        Core.forEachChild(e, child -> collectCalls(child, methods, out));
    }

    private static String methodOf(Core.Call call, Predicate<String> isAMethod) {
        // What a call reaches that a method of this module might run: a helper it carries, or
        // one of its values. Every other callee runs somewhere a method here is not.
        ReachName.Declaration held = switch (call.fn()) {
            case Core.Reached.OfDeclaration named -> named.name();
            case Core.Reached.OfValue value -> value.name();
            case Core.Reached.OfPublishedValue _, Core.Reached.OfKernel _, Core.Emitted _ -> null;
        };
        if (held == null) {
            return null;
        }
        String text = DefinitionName.of(held).text();
        return isAMethod.test(text) ? text : null;
    }
}
