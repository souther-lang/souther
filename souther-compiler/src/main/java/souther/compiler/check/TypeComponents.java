package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The declarations that have to be answered together, and the order the rest can be answered in.
 *
 * <p>A type written in terms of another is answered once that other one is. Where two are written in
 * terms of each other there is no such order, and the only way to answer either is to answer both at
 * once by rising from "no value" until neither moves. Telling the two apart is what this is for: what
 * is left is a walk in one direction, and rising is kept for the places that need it.
 *
 * <p>Handed back with every component before any that reads it. An edge here runs from the
 * declaration to what it reads, so a component is complete once everything it reaches is.
 */
final class TypeComponents {

    private final Map<TypeSymbol, Set<TypeSymbol>> edges;
    private final Map<TypeSymbol, Integer> reached = new HashMap<>();
    private final Map<TypeSymbol, Integer> lowest = new HashMap<>();
    private final Deque<TypeSymbol> standing = new ArrayDeque<>();
    private final Set<TypeSymbol> onStand = new HashSet<>();
    private final List<List<TypeSymbol>> found = new ArrayList<>();
    private int next;

    private TypeComponents(Map<TypeSymbol, Set<TypeSymbol>> edges) {
        this.edges = edges;
    }

    /** The components of {@code edges}, each one before any component that reads it. */
    static List<List<TypeSymbol>> of(Map<TypeSymbol, Set<TypeSymbol>> edges) {
        TypeComponents walk = new TypeComponents(edges);
        for (TypeSymbol each : edges.keySet()) {
            if (!walk.reached.containsKey(each)) {
                walk.walk(each);
            }
        }
        return walk.found;
    }

    /** Whether {@code component} is one that has to be risen through rather than read once. */
    static boolean recurses(List<TypeSymbol> component, Map<TypeSymbol, Set<TypeSymbol>> edges) {
        return component.size() > 1
                || edges.getOrDefault(component.get(0), Set.of()).contains(component.get(0));
    }

    private void walk(TypeSymbol from) {
        reached.put(from, next);
        lowest.put(from, next);
        next++;
        standing.push(from);
        onStand.add(from);
        for (TypeSymbol each : edges.getOrDefault(from, Set.of())) {
            if (!reached.containsKey(each)) {
                walk(each);
                lowest.put(from, Math.min(lowest.get(from), lowest.get(each)));
            } else if (onStand.contains(each)) {
                lowest.put(from, Math.min(lowest.get(from), reached.get(each)));
            }
        }
        if (lowest.get(from).equals(reached.get(from))) {
            List<TypeSymbol> component = new ArrayList<>();
            TypeSymbol each;
            do {
                each = standing.pop();
                onStand.remove(each);
                component.add(each);
            } while (!each.equals(from));
            found.add(List.copyOf(component));
        }
    }
}
