package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
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

    private TypeComponents() {}

    /**
     * The components of {@code edges}, each one before any component that reads it.
     *
     * <p><b>Walked by the names, and not in the order the graph was built.</b> Which component is
     * found first, and which member of one stands first inside it, are decided by the order the
     * walk reaches things — and a mapping keyed by a declaration cannot see the order it was
     * filled in, so two callers holding the same graph could be answered two different ways with
     * nothing able to tell them apart. Both places the walk chooses from are ordered here, so the
     * answer is a function of the graph.
     *
     * <p>Ordered where the walk reads rather than sorted afterwards. What comes back is in an
     * order — every component before any that reads it — and sorting the components would be
     * answering a different question with the same shape.
     */
    static List<List<TypeSymbol>> of(Map<TypeSymbol, Set<TypeSymbol>> edges) {
        Map<TypeSymbol, List<TypeSymbol>> ordered = new LinkedHashMap<>();
        for (TypeSymbol each : inOneOrder(edges.keySet())) {
            ordered.put(each, inOneOrder(edges.get(each)));
        }
        List<List<TypeSymbol>> found = new ArrayList<>();
        for (List<TypeSymbol> each : Cycles.components(ordered)) {
            // Under the names, because the order the walk leaves them in is the order it happened
            // to reach them and members of one component reach each other — there is no order
            // among them for it to be. The order between components is another question and is
            // what the list they are added to answers.
            found.add(inOneOrder(each));
        }
        return found;
    }

    /** The same declarations, in the one order their names put them in. */
    private static List<TypeSymbol> inOneOrder(Collection<TypeSymbol> named) {
        List<TypeSymbol> out = new ArrayList<>(named);
        out.sort(null);
        return List.copyOf(out);
    }

    /** Whether {@code component} is one that has to be risen through rather than read once. */
    static boolean recurses(List<TypeSymbol> component, Map<TypeSymbol, Set<TypeSymbol>> edges) {
        return component.size() > 1
                || edges.getOrDefault(component.get(0), Set.of()).contains(component.get(0));
    }
}
