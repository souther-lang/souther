package souther.compiler.coverage;

import souther.compiler.check.Comparison;
import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.types.CoverageOrigin;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
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
 *
 * <p><b>The node gets a reader in and goes no further.</b> A walk over the tree — the emitter, the
 * numbering — meets a node and has to ask which comparison it is, and {@link #occurrenceAt} is that
 * question. What comes back is a {@link ComparisonOccurrence}, which is what every reader below
 * joins on, and there is no way back from one to the node it was found at. That is what stops the
 * tree being the join key: a reader holding an occurrence cannot fall back on matching objects, and
 * cannot go to the node for an operator the recognition has already read.
 */
public final class ComparisonCatalog {

    /**
     * One comparison of one body, as the source wrote it.
     *
     * <p>Occurrence and not comparison. A non-recursive helper is spliced into each body that calls
     * it, so one comparison the author wrote stands here once per call — each reached under its
     * caller's own conditions, and each its own thing to say something about.
     *
     * @param which      which comparison of which body this is, which is what every reader joins on
     * @param comparison what the recognition established: what the operator placed, and the two
     *                   sides it placed it on. Recognising the node as a comparison is what puts it
     *                   here, so what the recognition established travels with it and a reader
     *                   below has no operator left to read again
     * @param at         where it is written, as a report may say it. A {@link Citation} and not a
     *                   position, because a comparison spliced in from another module is written in
     *                   that module's file and reached from a call in this one — and it is here
     *                   rather than taken again wherever a report needs one, so that a rule and the
     *                   line it draws are found at one place because they read one answer
     * @param origin     what wrote it, which is how a report names the rule it states. Beside the
     *                   citation because they are one question — which written thing this is — and
     *                   a reader that had to go to the tree for either would have the tree, and
     *                   with it everything the recognition already answered
     */
    public record Catalogued(ComparisonOccurrence which, Comparison comparison, Citation at,
                             CoverageOrigin origin) {

        public Catalogued {
            if (which == null || comparison == null || at == null || origin == null) {
                throw new IllegalArgumentException(
                        "a catalogued comparison is one comparison, named, placed and attributed");
            }
        }
    }

    /** How a walk over the tree gets in, and the whole of what the node is used for. */
    private final IdentityHashMap<Core, ComparisonOccurrence> occurrenceAtNode;

    /** What the module holds, under the names this issued. */
    private final Map<ComparisonOccurrence, Catalogued> byOccurrence;

    private ComparisonCatalog(IdentityHashMap<Core, ComparisonOccurrence> occurrenceAtNode,
                              Map<ComparisonOccurrence, Catalogued> byOccurrence) {
        this.occurrenceAtNode = occurrenceAtNode;
        this.byOccurrence = byOccurrence;
    }

    /** The comparisons of every behavior body of one module. */
    public static ComparisonCatalog of(Map<String, Core> behaviorBodies) {
        IdentityHashMap<Core, ComparisonOccurrence> occurrenceAtNode = new IdentityHashMap<>();
        Map<ComparisonOccurrence, Catalogued> byOccurrence = new LinkedHashMap<>();
        for (Map.Entry<String, Core> body : behaviorBodies.entrySet()) {
            // The nodes in the order the source wrote them, each with what recognising it
            // established. Recognised once and here: gathered as nodes and recognised again where
            // the name is made, this would be the same question asked twice about one binary, with
            // a case to answer for the second answer being different.
            List<Map.Entry<Core.Binary, Comparison>> found = new ArrayList<>();
            walk(body.getValue(), found);
            for (int ordinal = 0; ordinal < found.size(); ordinal++) {
                Core.Binary binary = found.get(ordinal).getKey();
                ComparisonOccurrence which =
                        new ComparisonOccurrence(body.getKey(), ordinal);
                occurrenceAtNode.put(binary, which);
                byOccurrence.put(which, new Catalogued(which, found.get(ordinal).getValue(),
                        Citation.of(binary.pos()), binary.origin()));
            }
        }
        return new ComparisonCatalog(occurrenceAtNode, byOccurrence);
    }

    private static void walk(Core e, List<Map.Entry<Core.Binary, Comparison>> found) {
        // What a representation kept standing for an analysis to read. What a run does is measured
        // over the tree that runs, which keeps none of these, so reaching one would mean this
        // enumeration was taken over a tree nothing executes.
        if (e instanceof Core.PreservedCall preserved) {
            throw preserved.unexpectedIn("the comparisons of a body");
        }
        if (e instanceof Core.Binary binary && binary.origin() != null
                && binary.origin().isWritten()) {
            Comparison.of(binary).ifPresent(
                    comparison -> found.add(Map.entry(binary, comparison)));
        }
        Core.forEachChild(e, child -> walk(child, found));
    }

    /**
     * Which comparison {@code node} is, or empty where it is not one of this module's.
     *
     * <p>What a walk over the tree asks instead of matching on the shape of the node. Empty is the
     * answer for a node that is not a comparison, for one written where this compile has no source,
     * and for one standing in a tree this catalog was not taken over — three things a reader
     * deciding for itself would have had to remember to ask about separately.
     */
    public Optional<ComparisonOccurrence> occurrenceAt(Core node) {
        return Optional.ofNullable(occurrenceAtNode.get(node));
    }

    /** The same, together with what was recognised there and where it is written. */
    public Optional<Catalogued> at(Core node) {
        return occurrenceAt(node).map(byOccurrence::get);
    }

    /**
     * What {@code which} names.
     *
     * <p>Total for an occurrence this catalog issued, which is the only kind a reader of the
     * compiler is handed. So there is no answer for one of those not to have, and an occurrence
     * made anywhere else — another module's catalog, or a fixture — is a mistake this says out loud
     * rather than an empty a caller writes a branch for.
     */
    public Catalogued of(ComparisonOccurrence which) {
        Catalogued held = byOccurrence.get(which);
        if (held == null) {
            throw new IllegalArgumentException(
                    "no comparison of this module is " + which);
        }
        return held;
    }

    /** Every comparison the module holds, in the order the bodies were walked. */
    public List<Catalogued> all() {
        return List.copyOf(byOccurrence.values());
    }
}
