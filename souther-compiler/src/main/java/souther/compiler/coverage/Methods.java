package souther.compiler.coverage;

import souther.compiler.ast.DefinitionName;
import souther.compiler.core.Core;
import souther.compiler.types.ReachName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The values of a module the backend emits as a method of its own, and which of them each behavior
 * calls.
 *
 * <p>What a behavior emits is its own body and the body of every method it calls, directly or
 * through another. A method is one body with one set of probes however many behaviors call it, so
 * the places it holds are physically in it and are owed by each behavior that reaches it. Which
 * bodies those are is asked here and nowhere else: a reader that took a behavior's body alone would
 * be looking for a comparison in a body that does not hold it.
 *
 * <p>Which method a call runs is answered here too, and the closures are made of that answer. A
 * reader that goes into a method where a call runs it and a closure that says which methods a
 * behavior owes are one call graph read two ways; a reader deciding for itself which calls run a
 * method would be a second graph, agreeing with this one until a new kind of callee arrives.
 *
 * @param entries  each behavior's body, by the behavior's name
 * @param bodies   each method's body, by the name of the value
 * @param calls    the methods each body calls directly, behaviors and methods alike, by its name
 * @param calledBy the methods each behavior calls, directly or through another, by the behavior's
 *                 name
 */
record Methods(Map<String, Core> entries, Map<String, Core> bodies,
               Map<String, Set<String>> calls, Map<String, Set<String>> calledBy) {

    /** A module with no method, which is what a hand-built plan holds. */
    static final Methods NONE = new Methods(Map.of(), Map.of(), Map.of(), Map.of());

    /** The methods of {@code module}, and which of its behaviors call which. */
    static Methods of(ModuleBodies module) {
        Map<String, Set<String>> direct = new LinkedHashMap<>();
        module.bodies().forEach((name, body) -> direct.put(name, callsOf(body, module.methods())));
        module.methods().forEach((name, body) -> direct.put(name, callsOf(body, module.methods())));
        Map<String, Set<String>> reached = new LinkedHashMap<>();
        for (String behavior : module.bodies().keySet()) {
            Set<String> all = new LinkedHashSet<>();
            Deque<String> pending = new ArrayDeque<>(direct.get(behavior));
            while (!pending.isEmpty()) {
                String next = pending.removeFirst();
                if (all.add(next)) {
                    pending.addAll(direct.get(next));
                }
            }
            reached.put(behavior, Collections.unmodifiableSet(all));
        }
        return new Methods(Collections.unmodifiableMap(new LinkedHashMap<>(module.bodies())),
                Map.copyOf(module.methods()), Map.copyOf(direct), Map.copyOf(reached));
    }

    /**
     * Whether {@code behavior} owes what the body named {@code body} holds: its own, and the
     * methods it calls'.
     */
    boolean owes(String behavior, String body) {
        return body.equals(behavior) || calledBy.getOrDefault(behavior, Set.of()).contains(body);
    }

    /** The methods {@code emitted} calls, directly or through another, whichever behavior it is. */
    List<Core> calledFrom(Core emitted) {
        Set<String> reached = new LinkedHashSet<>();
        Deque<String> pending = new ArrayDeque<>(callsOf(emitted, bodies));
        while (!pending.isEmpty()) {
            String next = pending.removeFirst();
            if (reached.add(next)) {
                pending.addAll(callsOf(bodies.get(next), bodies));
            }
        }
        List<Core> out = new ArrayList<>();
        reached.forEach(name -> out.add(bodies.get(name)));
        return out;
    }

    /**
     * The bodies a run of {@code behavior} goes through: its own, then each method it calls with
     * every method that calls it before it.
     *
     * <p>In that order because a reader carrying what holds where a call is made into the method it
     * runs has to have read every such call before it reads the method. A value takes no argument
     * and so cannot reach itself, which is what makes the order exist.
     *
     * @param plan the plan these are the methods of, which the run is read against
     */
    RunBodies run(String behavior, CoverageSites.Plan plan) {
        List<String> finished = new ArrayList<>();
        Set<String> visited = new HashSet<>();
        for (String callee : calls.getOrDefault(behavior, Set.of())) {
            finish(callee, visited, finished);
        }
        Map<String, Core> inOrder = new LinkedHashMap<>();
        for (String name : finished.reversed()) {
            inOrder.put(name, bodies.get(name));
        }
        return new RunBodies(entries.get(behavior), inOrder, this, plan);
    }

    /** {@code name} after every method it calls, which is reversed into callers first. */
    private void finish(String name, Set<String> visited, List<String> finished) {
        if (!visited.add(name)) {
            return;
        }
        for (String callee : calls.get(name)) {
            finish(callee, visited, finished);
        }
        finished.add(name);
    }

    /** The name of the method of this module {@code call} runs, or null where it runs none. */
    String methodOf(Core.Call call) {
        return methodOf(call, bodies);
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
            String called = methodOf(call, methods);
            if (called != null) {
                out.add(called);
            }
        }
        Core.forEachChild(e, child -> collectCalls(child, methods, out));
    }

    private static String methodOf(Core.Call call, Map<String, Core> methods) {
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
        return methods.containsKey(text) ? text : null;
    }
}
