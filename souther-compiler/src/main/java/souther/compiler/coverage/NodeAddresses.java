package souther.compiler.coverage;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Where every place of one body is, and where every name it binds stands, worked out in one descent.
 *
 * <p>One descent and not two. Where a place is and where a binder stands are the same question asked
 * of the same walk — a binder is at a slot of a node, and the node is at an address — and two walks
 * answering them would be two answers to what a body holds, each with its own idea of what to do
 * with a node that several ways lead to.
 *
 * <p>Keyed by identity, because this is the one crossing from a walk that holds the tree to an
 * address that does not need it. A caller has a node — it is walking the body the numbering was
 * taken over — and wants what that node's place is called; two nodes that look alike are two places
 * and a value-keyed map would give the first one's answer for the second.
 *
 * <p><b>Every way to a place.</b> The descent goes down each slot once from each way it arrived, so
 * a node several slots lead to collects each arrival. That is the size of the answer rather than a
 * cost on the way to it: a place several ways lead to <em>is</em> several ways, and there is no cap
 * — a limit here would be this refusing bodies rather than describing them.
 */
final class NodeAddresses {

    private final String behavior;

    private final Map<Core, Set<CorePath>> waysTo = new IdentityHashMap<>();

    /** Where each name the body binds is bound, kept as the node and slot until the descent is done
     *  — a binder's address is its owner's, and the owner's is not settled until every way to it has
     *  been arrived at. */
    private final List<StandingAt> binders = new ArrayList<>();

    private record StandingAt(souther.compiler.types.BindingId binding, Core owner,
                              BinderSlot slot) {}

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
        if (ways.size() == 1) {
            // The names this node opens, taken once however many ways lead to it: a node met again
            // is the same node and binds the same names at the same slots.
            binderSlots(at);
        }
        for (CoreStructure.Child child : CoreStructure.childrenOf(at)) {
            walk(child.node(), here.then(child.edge()));
        }
    }

    private void binderSlots(Core at) {
        switch (at) {
            case Core.LetIn it -> keep(it.binder(), it, new BinderSlot.LetBinder());
            case Core.Block it -> {
                for (int i = 0; i < it.params().size(); i++) {
                    keep(it.params().get(i), it, new BinderSlot.BlockParam(i));
                }
            }
            case Core.Match it -> {
                for (int i = 0; i < it.cases().size(); i++) {
                    keep(it.cases().get(i).binder(), it, new BinderSlot.CaseBinder(i));
                }
            }
            case Core.IfConstructed it ->
                    keep(it.binder(), it, new BinderSlot.ConstructedBinder());
            default -> { }
        }
    }

    private void keep(Core.Binder binder, Core owner, BinderSlot slot) {
        if (binder != null && binder.binding() != null) {
            binders.add(new StandingAt(binder.binding(), owner, slot));
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

    /** Whose body these are of. */
    String behavior() {
        return behavior;
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

    /** Where each name the body binds stands, now that every way to every owner is known. */
    Map<souther.compiler.types.BindingId, BinderAddress> bound() {
        Map<souther.compiler.types.BindingId, BinderAddress> out = new LinkedHashMap<>();
        for (StandingAt each : binders) {
            BinderAddress where = new BinderAddress.Local(of(each.owner()), each.slot());
            BinderAddress already = out.put(each.binding(), where);
            // Two binders under one name is a body whose reads cannot say which they mean. Told by
            // the places being different rather than by there being a second answer: a node several
            // ways lead to is arrived at once here, and asking twice about one binder is not a
            // second binder.
            if (already != null && !already.equals(where)) {
                throw new IllegalStateException("`" + behavior + "` binds " + each.binding()
                        + " at " + already + " and again at " + where);
            }
        }
        return out;
    }
}
