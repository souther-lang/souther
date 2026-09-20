package souther.compiler.coverage;

import souther.compiler.ast.DefinitionName;
import souther.compiler.core.Core;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
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
 * @param bodies each method's body, by the name of the value
 * @param calledBy the methods each behavior calls, directly or through another, by the behavior's
 *                 name
 */
record Methods(Map<String, Core> bodies, Map<String, Set<String>> calledBy) {

    /** A module with no method, which is what a hand-built plan holds. */
    static final Methods NONE = new Methods(Map.of(), Map.of());

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
        return new Methods(Map.copyOf(module.methods()), Map.copyOf(reached));
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
        if (e instanceof Core.Call call && call.fn() instanceof Core.Reached.OfDeclaration named) {
            String text = DefinitionName.of(named.name()).text();
            if (methods.containsKey(text)) {
                out.add(text);
            }
        }
        Core.forEachChild(e, child -> collectCalls(child, methods, out));
    }
}
