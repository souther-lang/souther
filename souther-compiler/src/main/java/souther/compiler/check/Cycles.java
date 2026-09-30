package souther.compiler.check;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which nodes of a directed graph lie on a cycle, and a way round one.
 *
 * <p>The graphs handed here are the ones a module's declarations make, and a module chains its
 * declarations as long as it likes. Every walk holds its own stack for that reason: one on the call
 * stack answers a long chain by running out of room, and then what a module means depends on the
 * thread that compiled it.
 *
 * <p>Which nodes are on a cycle is answered once over the whole graph. Asked of each node in turn, a
 * search walks everything that node reaches, which over a chain is the rest of the chain again for
 * every link.
 */
final class Cycles {

    private Cycles() {}

    /**
     * Each node of {@code edges} that reaches itself, mapped to the nodes it lies on a cycle with,
     * itself among them: a strongly connected group of more than one, or one node with an edge to
     * itself. A node on no cycle is not a key.
     *
     * <p>Every member of one group maps to the same set. Tarjan's, written with its own stack.
     */
    static <N> Map<N, Set<N>> groups(Map<N, ? extends Collection<N>> edges) {
        Map<N, Integer> index = new LinkedHashMap<>();
        Map<N, Integer> low = new LinkedHashMap<>();
        Set<N> open = new LinkedHashSet<>();       // on the component stack
        List<N> component = new ArrayList<>();
        Map<N, Set<N>> found = new LinkedHashMap<>();
        int next = 0;
        for (N root : edges.keySet()) {
            if (index.containsKey(root)) {
                continue;
            }
            List<Walking<N>> frames = new ArrayList<>();
            frames.add(new Walking<>(root, edgesOf(edges, root).iterator()));
            index.put(root, next);
            low.put(root, next++);
            open.add(root);
            component.add(root);
            while (!frames.isEmpty()) {
                Walking<N> frame = frames.getLast();
                N at = frame.node();
                if (frame.edges().hasNext()) {
                    N to = frame.edges().next();
                    if (!index.containsKey(to)) {
                        index.put(to, next);
                        low.put(to, next++);
                        open.add(to);
                        component.add(to);
                        frames.add(new Walking<>(to, edgesOf(edges, to).iterator()));
                    } else if (open.contains(to)) {
                        low.put(at, Math.min(low.get(at), index.get(to)));
                    }
                    continue;
                }
                frames.removeLast();
                if (!frames.isEmpty()) {
                    N under = frames.getLast().node();
                    low.put(under, Math.min(low.get(under), low.get(at)));
                }
                if (low.get(at).equals(index.get(at))) {
                    Set<N> group = new LinkedHashSet<>();
                    N popped;
                    do {
                        popped = component.removeLast();
                        open.remove(popped);
                        group.add(popped);
                    } while (!popped.equals(at));
                    // One node is a group of its own unless it names itself: a group of one has no
                    // way round except an edge back to where it started.
                    if (group.size() > 1 || edgesOf(edges, at).contains(at)) {
                        Set<N> fixed = Collections.unmodifiableSet(group);
                        for (N member : group) {
                            found.put(member, fixed);
                        }
                    }
                }
            }
        }
        return found;
    }

    /**
     * A way from {@code start} back to it, both ends included, or an empty list where there is none.
     *
     * <p>The first way a depth-first walk meets, taking each node's edges in the order the graph
     * holds them, so the same graph always names the same way round.
     */
    static <N> List<N> roundFrom(N start, Map<N, ? extends Collection<N>> edges) {
        Set<N> seen = new HashSet<>();
        seen.add(start);
        List<N> path = new ArrayList<>();
        path.add(start);
        List<Iterator<N>> left = new ArrayList<>();
        left.add(edgesOf(edges, start).iterator());
        while (!left.isEmpty()) {
            Iterator<N> here = left.getLast();
            if (!here.hasNext()) {
                left.removeLast();
                path.removeLast();
                continue;
            }
            N next = here.next();
            if (next.equals(start)) {
                path.add(start);
                return path;
            }
            if (seen.add(next)) {
                path.add(next);
                left.add(edgesOf(edges, next).iterator());
            }
        }
        return List.of();
    }

    private static <N> Collection<N> edgesOf(Map<N, ? extends Collection<N>> edges, N node) {
        Collection<N> out = edges.get(node);
        return out == null ? List.of() : out;
    }

    /**
     * A node the walk is inside, and the edges of it that are left.
     *
     * <p>The iterator is the frame's, taken once when the frame is pushed. A frame is resumed once
     * per edge it has, so a frame that worked out where it had got to would read the node's edges
     * once per edge — which over a node that reaches many is that node's edges squared, and a chain
     * says nothing about it because every node there reaches one.
     */
    private record Walking<N>(N node, Iterator<N> edges) {}
}
