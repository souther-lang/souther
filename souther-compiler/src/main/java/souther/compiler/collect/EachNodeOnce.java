package souther.compiler.collect;

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

/**
 * What one walk over a graph works out of each node, worked out once however many ways lead to
 * the node.
 *
 * <p>A name used twice holds one object in two places, so the derivations, conditions, reads and
 * statements made from it are graphs, and the ways down a chain of names each using the one before
 * it twice are two to the depth. A walk that recurses into such a structure for itself pays for
 * every way; asked here, it pays for every node. The walk owns what it keeps: one of these is made
 * for a question, answers it, and is let go, so what a node came to is never read under another
 * question's premises.
 *
 * <p>Nodes are told apart by identity. Two equal nodes made apart are two nodes here, and what is
 * worked out of each is the same for both only where the walk's answer is a function of the
 * node's value; a walk whose answer is not that keeps a node for each way it is made.
 *
 * <p>The recursion {@code work} makes into the nodes below is {@link #of} again. It is held in
 * the map only when {@code work} returns, so a node reached from inside its own work is worked
 * out afresh: that is a cycle, and a graph of reads has none.
 *
 * <p>Not thread-safe: a walk is one thread's.
 *
 * @param <N> the node
 * @param <R> what is worked out of it
 */
public final class EachNodeOnce<N, R> {

    private final Map<N, R> worked = new IdentityHashMap<>();

    /** What {@code work} says of {@code node}: worked out the first time it is asked, and the same
     *  answer after. */
    public R of(N node, Function<N, R> work) {
        R known = worked.get(node);
        if (known != null) {
            return known;
        }
        R made = work.apply(node);
        // A node with no answer would be worked out again each time it is asked, which is the
        // cost of every way down to it that this is for.
        worked.put(node, Objects.requireNonNull(made,
                "what is worked out of a node is some answer; one that is none is a value of its"
                        + " own (an Optional)"));
        return made;
    }
}
