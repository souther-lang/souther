package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Where the walk of a body met each construction in it: what stood on the way to it, and the
 * names as they stand there.
 *
 * <p>What the walk says and nobody else, as {@link WaysToNodes} is for the parts of a condition:
 * it is the walk that meets the arm of a choice under what the arm proves, and the right of an
 * {@code &&} under the left coming out true, so a construction on an arm is met under the arm's
 * condition. A reader that asks whether a run gets to a construction, and which, asks for its way
 * here and not a second account of where evaluation goes.
 *
 * <p>Of the behavior's own body only: a helper's body read at a call, and a template, are read
 * under ways that are not one run of this body.
 *
 * <p>Complete once the walk is, and shared by every reading of the body it is made for.
 */
final class WhereConstructionsAreMet {

    /** Where the walk met a construction: the way to it and the names there. */
    record Met(List<OnTheWay> way, InputReads reads) {

        Met {
            way = List.copyOf(way);
        }
    }

    private final Map<Core.Construct, List<Met>> met = new IdentityHashMap<>();

    /** That the walk met {@code made} on {@code way}, with the names as {@code reads} has them. */
    void met(Core.Construct made, List<OnTheWay> way, InputReads reads) {
        met.computeIfAbsent(made, _ -> new ArrayList<>(1)).add(new Met(way, reads));
    }

    /**
     * Where the walk met {@code made}, where it met it once: empty where it never did, or did more
     * than once, as a construction in a closure read on each application is, which is no one way.
     */
    Optional<Met> at(Core.Construct made) {
        List<Met> found = met.get(made);
        return (found == null || found.size() != 1) ? Optional.empty()
                : Optional.of(found.getFirst());
    }
}
