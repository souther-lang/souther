package souther.compiler.coverage;

import souther.compiler.core.Core;
import souther.compiler.diag.Citation;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Which comparisons the bodies of a module hold, as a fact about the bodies.
 *
 * <p>One answer, and everything that asks about a comparison asks this. A number is handed out for
 * one, a line is drawn on one, a run is proved never to reach one, and a path is named by one — four
 * readers that each used to decide for themselves what a comparison is, by descending {@code &&} and
 * {@code ||} from a fork's condition. Four descents of one shape are four sets that can drift apart,
 * and the one they agreed on was not the comparisons of a body: it was the comparisons a fork was
 * written directly around.
 *
 * <p>So where a comparison stands is not part of this. {@code a > 1} tested by an {@code if}, given
 * a name a line above it, returned as the behavior's answer, or written inside a function value
 * handed to a combinator is one construct put to four uses — and which use it was put to is a
 * question about the body that the readings answer, each in its own terms.
 *
 * <p>Atomic and no wider. {@code &&} and {@code ||} combine comparisons rather than being ones, and
 * {@code +} is not one at all; what this holds is exactly what leaves a truth on the stack for a
 * probe to copy, which is what lets the numbering be checked rather than remembered.
 */
public final class ComparisonCatalog {

    /**
     * One comparison of one body, as the source wrote it.
     *
     * <p>Occurrence and not comparison. A non-recursive helper is spliced into each body that calls
     * it, so one comparison the author wrote stands here once per call — each reached under its
     * caller's own conditions, and each its own thing to say something about.
     *
     * @param behavior which body it stands in
     * @param node     the comparison itself, which is what every reader joins on. Held by identity:
     *                 Core nodes are records, so two comparisons that look the same are equal, and a
     *                 reader handed the wrong one of two would be answering about the other body
     * @param at       where it is written, as a report may say it. A {@link Citation} and not a
     *                 position, because a comparison spliced in from another module is written in
     *                 that module's file and reached from a call in this one
     * @param ordinal  where it comes among the comparisons of this module, in the order the bodies
     *                 are declared and, within one, the order the source wrote them
     */
    public record Comparison(String behavior, Core.Binary node, Citation at, int ordinal) {}

    private final List<Comparison> comparisons;
    private final IdentityHashMap<Core, Comparison> byNode;

    private ComparisonCatalog(List<Comparison> comparisons,
                              IdentityHashMap<Core, Comparison> byNode) {
        this.comparisons = List.copyOf(comparisons);
        this.byNode = byNode;
    }

    /** The comparisons of every behavior body of one module, in the order the source wrote them. */
    public static ComparisonCatalog of(Map<String, Core> behaviorBodies) {
        List<Comparison> found = new ArrayList<>();
        IdentityHashMap<Core, Comparison> byNode = new IdentityHashMap<>();
        for (Map.Entry<String, Core> body : behaviorBodies.entrySet()) {
            walk(body.getKey(), body.getValue(), found, byNode);
        }
        return new ComparisonCatalog(found, byNode);
    }

    private static void walk(String behavior, Core e, List<Comparison> found,
                             IdentityHashMap<Core, Comparison> byNode) {
        // What a representation kept standing for an analysis to read. What a run does is measured
        // over the tree that runs, which keeps none of these, so reaching one would mean this
        // enumeration was taken over a tree nothing executes.
        if (e instanceof Core.PreservedCall preserved) {
            throw preserved.unexpectedIn("the comparisons of a body");
        }
        if (e instanceof Core.Binary binary && binary.op().compares()
                && binary.origin() != null && binary.origin().isWritten()) {
            Comparison comparison = new Comparison(behavior, binary,
                    Citation.of(binary.pos()), found.size());
            found.add(comparison);
            byNode.put(binary, comparison);
        }
        Core.forEachChild(e, child -> walk(behavior, child, found, byNode));
    }

    /** Every comparison of the module, in the order the source wrote them. */
    public List<Comparison> comparisons() {
        return comparisons;
    }

    /**
     * Which comparison {@code node} is, or empty where it is not one of this module's.
     *
     * <p>What a reader asks instead of matching on the shape of the node. Empty is the answer for a
     * node that is not a comparison, for one written where this compile has no source, and for one
     * standing in a tree this catalog was not taken over — three things a reader deciding for itself
     * would have had to remember to ask about separately.
     */
    public Optional<Comparison> at(Core node) {
        return Optional.ofNullable(byNode.get(node));
    }
}
