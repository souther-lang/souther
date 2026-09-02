package souther.compiler.coverage;

import souther.compiler.core.Core;

import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Where every place of one body is, worked out once.
 *
 * <p>Keyed by identity, because this is the one crossing from a walk that holds the tree to an
 * address that does not need it. A caller has a node — it is walking the body the numbering was
 * taken over — and wants what that node's place is called; two nodes that look alike are two places
 * and a value-keyed map would give the first one's answer for the second.
 *
 * <p><b>Every way to a place, gathered on the way down.</b> The walk descends each slot once, so a
 * node several slots lead to is arrived at several times and its address collects each arrival.
 * There is no cap: a place with more ways to it than a reader expected is a fact about the body, and
 * a limit here would be this reading refusing bodies rather than describing them.
 */
final class NodeAddresses {

    private final String behavior;

    private final Map<Core, Set<CorePath>> waysTo = new IdentityHashMap<>();

    private NodeAddresses(String behavior) {
        this.behavior = behavior;
    }

    /** The addresses of every place in {@code body}, which is {@code behavior}'s. */
    static NodeAddresses of(String behavior, Core body) {
        NodeAddresses out = new NodeAddresses(behavior);
        out.walk(body, CorePath.ROOT);
        return out;
    }

    private void walk(Core at, CorePath here) {
        Set<CorePath> ways = waysTo.computeIfAbsent(at, _ -> new LinkedHashSet<>());
        if (!ways.add(here)) {
            return;   // this same way down, met again: nothing below it is new either
        }
        for (CoreStructure.Child child : CoreStructure.childrenOf(at)) {
            walk(child.node(), here.then(child.edge()));
        }
    }

    /**
     * What {@code node}'s place is called, for a node of the body this was taken over.
     *
     * <p>Throws for a node from anywhere else. A walk asking this is walking the body these
     * addresses are of, so a node they do not hold is a walk over other trees than these — and an
     * address invented for it would name a place in a body nobody is talking about.
     */
    NodeAddress of(Core node) {
        Set<CorePath> ways = waysTo.get(node);
        if (ways == null) {
            throw new IllegalStateException("no place in `" + behavior + "` is a "
                    + node.getClass().getSimpleName() + " at " + node.pos()
                    + "; these addresses were taken over other trees than the one asking");
        }
        return new NodeAddress(behavior, ways);
    }

    /** How many places the body has, which is what a reader of this counts over. */
    int size() {
        return waysTo.size();
    }

    /** Every place, for a reader that wants the whole of one body's addresses. */
    Map<Core, NodeAddress> all() {
        Map<Core, NodeAddress> out = new IdentityHashMap<>();
        waysTo.forEach((node, ways) -> out.put(node, new NodeAddress(behavior, ways)));
        return out;
    }
}
