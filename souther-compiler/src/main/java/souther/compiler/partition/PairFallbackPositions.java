package souther.compiler.partition;

import souther.compiler.check.RuleRef;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Decision;
import souther.compiler.reading.Factor;
import souther.compiler.reading.Interaction;
import souther.compiler.reading.Outcome;
import souther.compiler.reading.PathAccess;
import souther.compiler.reading.WayIn;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The positions a body draws a distinction about, which is what the pair space is over where there
 * is a body.
 *
 * <p>What a combination of two classes asks is that the behavior was tried with both at once, and
 * that is worth asking where the body tells the two apart. A position the body says nothing about
 * keeps the rows its own classes are owed and makes no combination with anything: the answer cannot
 * turn on it, so a row at such a combination shows nothing the two rows apart do not.
 *
 * <p><b>Two readings, because a body says so in two ways.</b> A decision names the position it
 * turns on — a {@code match} on a case, a comparison a fork is taken by — and a rule the body
 * writes divides a position into classes whether or not the walk that finds the decisions reaches
 * it. The predicate handed to a {@code List.filter} is the second without the first: the walk does
 * not enter a block, on purpose, and the comparison inside it still states what this behavior tells
 * apart about its input. Read off the decisions alone, a behavior whose whole discrimination is
 * written in such a block would be one the pair space says nothing about — which is this compiler's
 * reach deciding what the model is about.
 *
 * <p><b>And not where a value is used.</b> A position copied into the answer, or added to another,
 * is read by the body and distinguished by nothing. Which is why the second reading asks for a rule
 * the body <em>wrote</em> rather than for a class the position has: a sum divides a position by
 * being a sum, and a body that never looks at it has said nothing about it.
 */
public final class PairFallbackPositions {

    private PairFallbackPositions() {}

    /**
     * Which of {@code axes} some decision of the body is about.
     *
     * <p>By the axis a condition names, which is the same lookup that turns a condition into the
     * classes it leaves. A condition this compiler cannot name a position for is about none of
     * them: what it says is unknown rather than about everything, and reading it as everything
     * would put a position back into the space on the strength of something unread.
     */
    public static Set<AxisId> of(CoverageRead.Read read, List<Axis> axes) {
        Set<AxisId> out = new LinkedHashSet<>();
        // What the body wrote a rule about. A rule the author named — an invariant, an `ensures`
        // — says what the type or the answer holds and is no statement about what this behavior
        // tells apart; one written in a body is. Read off where the classes came from, which is
        // the cuts and the partings: a position divided by a comparison inside a predicate has its
        // classes from that comparison and no decision the walk above could reach.
        for (Axis axis : axes) {
            boolean written = axis.cuts().stream()
                    .flatMap(cut -> cut.origins().stream())
                    .anyMatch(origin -> origin.rule() instanceof RuleRef.Written)
                    || axis.divides().stream()
                            .anyMatch(origin -> origin.rule() instanceof RuleRef.Written);
            if (written) {
                out.add(axis.id());
            }
        }
        for (Interaction group : read.interactions()) {
            group.reach().forEach(each -> at(out, each.constrains(), axes));
            for (Factor factor : group.factors()) {
                for (Outcome outcome : factor.outcomes()) {
                    outcome.holds().forEach(each -> at(out, each.constrains(), axes));
                }
            }
        }
        read.arms().forEach((_, access) -> {
            if (access instanceof PathAccess.Ways(var ways, var _)) {
                for (WayIn way : ways) {
                    for (Decision each : way.decisions()) {
                        at(out, each.constrains(), axes);
                    }
                }
            }
        });
        return Set.copyOf(out);
    }

    /** The axis one condition is about, where this run measures the position it names. */
    private static void at(Set<AxisId> out, souther.compiler.reading.Condition condition,
                           List<Axis> axes) {
        int at = InteractionCells.positionOf(condition, axes);
        if (at >= 0) {
            out.add(axes.get(at).id());
        }
    }
}
