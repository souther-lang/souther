package souther.compiler.coverage;

import souther.compiler.check.Comparison;
import souther.compiler.core.Core;
import souther.compiler.diag.Citation;

import java.util.IdentityHashMap;
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
     * @param comparison the comparison itself, which is what every reader joins on, together with
     *                   what its operator placed. Recognising the node as a comparison is what puts
     *                   it here, so what the recognition established travels with it and a reader
     *                   below has no operator left to read again. Joined on by identity: Core nodes
     *                   are records, so two comparisons that look the same are equal, and a reader
     *                   handed the wrong one of two would be answering about the other body
     * @param at         where it is written, as a report may say it. A {@link Citation} and not a
     *                   position, because a comparison spliced in from another module is written in
     *                   that module's file and reached from a call in this one — and it is here
     *                   rather than taken again wherever a report needs one, so that a rule and the
     *                   line it draws are found at one place because they read one answer
     */
    public record Catalogued(Comparison comparison, Citation at) {

        /** The node itself, for a reader joining on the tree. */
        public Core.Binary node() {
            return comparison.at();
        }
    }

    private final IdentityHashMap<Core, Catalogued> byNode;

    private ComparisonCatalog(IdentityHashMap<Core, Catalogued> byNode) {
        this.byNode = byNode;
    }

    /** The comparisons of every behavior body of one module. */
    public static ComparisonCatalog of(Map<String, Core> behaviorBodies) {
        IdentityHashMap<Core, Catalogued> byNode = new IdentityHashMap<>();
        for (Core body : behaviorBodies.values()) {
            walk(body, byNode);
        }
        return new ComparisonCatalog(byNode);
    }

    private static void walk(Core e, IdentityHashMap<Core, Catalogued> byNode) {
        // What a representation kept standing for an analysis to read. What a run does is measured
        // over the tree that runs, which keeps none of these, so reaching one would mean this
        // enumeration was taken over a tree nothing executes.
        if (e instanceof Core.PreservedCall preserved) {
            throw preserved.unexpectedIn("the comparisons of a body");
        }
        if (e instanceof Core.Binary binary && binary.origin() != null
                && binary.origin().isWritten()) {
            Comparison.of(binary).ifPresent(comparison ->
                    byNode.put(binary, new Catalogued(comparison, Citation.of(binary.pos()))));
        }
        Core.forEachChild(e, child -> walk(child, byNode));
    }

    /**
     * Which comparison {@code node} is, or empty where it is not one of this module's.
     *
     * <p>What a reader asks instead of matching on the shape of the node. Empty is the answer for a
     * node that is not a comparison, for one written where this compile has no source, and for one
     * standing in a tree this catalog was not taken over — three things a reader deciding for itself
     * would have had to remember to ask about separately.
     */
    public Optional<Catalogued> at(Core node) {
        return Optional.ofNullable(byNode.get(node));
    }
}
