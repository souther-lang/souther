package souther.compiler.coverage;

import souther.compiler.core.Core;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;

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
            new RunBodies(null, Map.of(), Methods.NONE, CoverageSites.Plan.NONE);

    private final Core entry;

    /** Each method the run calls by the value's name, callers first. */
    private final SequencedMap<String, Core> methods;

    private final Set<Core> owed;

    private final Methods graph;

    private final CoverageSites.Plan plan;

    RunBodies(Core entry, Map<String, Core> methods, Methods graph, CoverageSites.Plan plan) {
        this.entry = entry;
        this.methods = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(methods));
        Set<Core> owed = Collections.newSetFromMap(new IdentityHashMap<>());
        owed.addAll(methods.values());
        this.owed = Collections.unmodifiableSet(owed);
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
        boolean same = graph.entries().get(behavior) == bodies.bodies().get(behavior)
                && graph.bodies().size() == bodies.methods().size();
        for (Map.Entry<String, Core> method : bodies.methods().entrySet()) {
            same &= graph.bodies().get(method.getKey()) == method.getValue();
        }
        if (!same) {
            throw new IllegalArgumentException("the plan beside the bodies of `" + behavior
                    + "` is not a plan of them");
        }
        return graph.run(behavior, plan);
    }

    /** The same bodies, read against {@code other}: a plan of the same trees that answers some
     *  question about them otherwise. */
    RunBodies under(CoverageSites.Plan other) {
        return new RunBodies(entry, methods, graph, other);
    }

    /**
     * The behavior's own body, where a run starts. Null where none came out, which is the hole a
     * body the check did not lower leaves: nothing is in it and nothing is numbered there.
     */
    public Core entry() {
        return entry;
    }

    /** The bodies of the methods the run calls, directly or through another, each after every
     *  method that calls it. */
    public List<Core> methods() {
        return List.copyOf(methods.values());
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
        Core body = graph.bodies().get(name);
        if (!owed.contains(body)) {
            throw new IllegalArgumentException("a call runs the method of `" + name
                    + "`, which no body of this run calls");
        }
        return Optional.of(body);
    }
}
