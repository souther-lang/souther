package souther.compiler.coverage;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The bodies one run of a behavior goes through, with the plan that numbered their places.
 *
 * <p>One value and not two, so a reader of a behavior's places reads the bodies those places are
 * in. Handed a body beside a plan, a reader could be reading one tree while the plan's arms for the
 * behavior are in another — which is what a reader that took the behavior's body alone was doing to
 * every arm in a value the behavior calls.
 *
 * <p>Made by whoever holds the bodies, and never by the plan. A plan is an index into the trees the
 * check made, and what is an index hands out no way into what it indexes; the check that owns the
 * trees hands them out, paired here with the index made of them.
 */
public final class RunBodies {

    /** The run of a behavior whose bodies did not come out: nothing in it and nothing numbered. */
    public static final RunBodies NONE =
            new RunBodies(null, List.of(), Methods.NONE, CoverageSites.Plan.NONE);

    private final Core entry;

    /** The methods the run goes through, a cycle of calls together, callers before callees. */
    private final List<List<Core>> groups;

    /** The first method of the group each method is in, which stands for the group. */
    private final Map<Core, Core> groupOf;

    private final Methods graph;

    private final CoverageSites.Plan plan;

    RunBodies(Core entry, List<List<Core>> groups, Methods graph, CoverageSites.Plan plan) {
        this.entry = entry;
        List<List<Core>> held = new ArrayList<>();
        Map<Core, Core> groupOf = new IdentityHashMap<>();
        for (List<Core> group : groups) {
            held.add(List.copyOf(group));
            for (Core member : group) {
                groupOf.put(member, group.getFirst());
            }
        }
        this.groups = List.copyOf(held);
        this.groupOf = Collections.unmodifiableMap(groupOf);
        this.graph = graph;
        this.plan = plan;
    }

    /**
     * The run of {@code behavior} through {@code bodies}, read against {@code plan}.
     *
     * <p>Refused where the plan is not of these bodies: its places are filed by which trees were put
     * in it, so a plan of other trees beside these would answer about nothing here.
     */
    public static RunBodies of(ModuleBodies bodies, CoverageSites.Plan plan, String behavior) {
        Methods graph = plan.methods();
        if (graph.entries().get(behavior) != bodies.bodies().get(behavior)
                || !sameTrees(graph.bodies(), bodies.methods())
                || !sameTrees(graph.passages(), bodies.passages())) {
            throw new IllegalArgumentException("the plan beside the bodies of `" + behavior
                    + "` is not a plan of them");
        }
        return graph.run(behavior, plan);
    }

    private static boolean sameTrees(Map<String, Core> held, Map<String, Core> given) {
        if (held.size() != given.size()) {
            return false;
        }
        for (Map.Entry<String, Core> each : given.entrySet()) {
            if (held.get(each.getKey()) != each.getValue()) {
                return false;
            }
        }
        return true;
    }

    /** The same bodies, read against {@code other}: a plan of the same trees that answers some
     *  question about them otherwise. */
    RunBodies under(CoverageSites.Plan other) {
        return new RunBodies(entry, groups, graph, other);
    }

    /**
     * The behavior's own body, where a run starts. Null where none came out, which is the hole a
     * body the check did not lower leaves: nothing is in it and nothing is numbered there.
     */
    public Core entry() {
        return entry;
    }

    /**
     * The methods the run goes through, directly or through another — values' and the helpers'
     * emitted as methods — each after every method that calls into it from outside a cycle of
     * calls it is on, and the methods of one cycle next to each other.
     */
    public List<Core> methods() {
        List<Core> out = new ArrayList<>();
        groups.forEach(out::addAll);
        return List.copyOf(out);
    }

    /**
     * The method standing for the cycle of calls {@code method} is on: itself, where it is on
     * none. Two methods with one answer are entered together — a run calling one from the other
     * came into the cycle from outside it first.
     */
    public Core cycleOf(Core method) {
        Core first = groupOf.get(method);
        if (first == null) {
            throw new IllegalArgumentException("a method no body of this run calls");
        }
        return first;
    }

    /** The plan that numbered the places of these bodies. */
    public CoverageSites.Plan plan() {
        return plan;
    }

    /**
     * The body of the method {@code call} runs, or none where it runs no method of the module.
     *
     * <p>Asked of a call in one of these bodies, so the method is one of {@link #methods}. A call
     * running a method that is not is a call from some other run's body.
     */
    public Optional<Core> invokedBy(Core.Call call) {
        String name = graph.methodOf(call);
        if (name == null) {
            return Optional.empty();
        }
        Core body = graph.bodies().containsKey(name) ? graph.bodies().get(name)
                : graph.passages().get(name);
        if (!groupOf.containsKey(body)) {
            throw new IllegalArgumentException("a call runs the method of `" + name
                    + "`, which no body of this run calls");
        }
        return Optional.of(body);
    }
}
