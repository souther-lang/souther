package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.coverage.ComparisonCatalog;
import souther.compiler.coverage.CoverageSites;

import java.util.ArrayList;
import java.util.List;

/**
 * Which of a body's comparisons a line may be drawn on.
 *
 * <p>A policy over {@link ComparisonCatalog} and not a second account of what a comparison is.
 * The catalog says what the body holds; this says which of those the rules of a model are read off,
 * and the two are different questions with different answers. Kept apart because the first is a fact
 * about the source and the second is a decision about what a model divides — and while they were one
 * walk, the decision was being made by whatever the numbering happened to reach.
 *
 * <p>What the policy is today: a comparison written in the condition of a fork whose arms a run can
 * be recorded in, reached through {@code &&} and {@code ||}. So a comparison given a name a line
 * above the fork that tests it draws no line, and neither does one returned as the answer or handed
 * to a combinator — which are comparisons the catalog holds, the numbering numbers and the reading
 * names. Widening that is a change to what the rules of a model divide rather than to what a body is
 * read as, and it is a change here.
 *
 * <p>What is not answered here is what reaching an arm of the fork proves about a comparison under
 * it. Under {@code A && (B || C)} the arms tell those three apart — the arm the whole condition
 * holds on proves {@code A} ran and {@code B} ran, and proves nothing about {@code C} — and no
 * measure asks: a row meets a line by lighting the comparison's own probe, which is a fact the
 * comparison records for itself. It is a relation between a comparison and one use of its truth, so
 * a comparison consumed by two forks has two answers and one consumed by none has no answer at all.
 * Anything modelling it belongs where the uses are, not here and not on the origin.
 */
final class BoundaryComparisons {

    /**
     * The comparisons of {@code iff}'s condition, in the order the source wrote them.
     *
     * <p>Descends through {@code &&} and {@code ||} only, which is what a condition is built out of.
     * Anything else is where the condition's operands stop, and whether one of those is a comparison
     * is the catalog's answer rather than a shape read off the node.
     */
    static List<Core.Binary> of(Core.If iff, ComparisonCatalog catalog) {
        List<Core.Binary> out = new ArrayList<>();
        placed(iff.cond(), catalog, out);
        return out;
    }

    private static void placed(Core e, ComparisonCatalog catalog, List<Core.Binary> out) {
        if (e instanceof Core.Binary binary
                && (binary.op() == Hir.BinOp.AND || binary.op() == Hir.BinOp.OR)) {
            placed(binary.left(), catalog, out);
            placed(binary.right(), catalog, out);
            return;
        }
        // Whether this is a comparison is the catalog's answer. Read off the node's own shape here,
        // this was a second account of what a comparison is — spelled as "a binary that is not
        // `&&` or `||`", which is every arithmetic node in the condition as well.
        catalog.at(e).ifPresent(comparison -> out.add(comparison.node()));
    }

    /**
     * The arms a row that reached this fork's condition can be recorded in, or null where none can.
     *
     * <p>What gates the policy and nothing more. A fork no run can be recorded in is one no line
     * drawn under it could ever be shown met, so the rules there are read and nothing is owed.
     */
    static CoverageSites.GuardRef guardOf(CoverageSites.Plan plan, Core.If iff) {
        int[] arms = plan.probesOf(iff);
        if (arms == null || arms.length != 2) {
            return null;
        }
        for (CoverageSites.GuardRef guard : plan.guards()) {
            if (guard.siteIndexThen() == arms[0] && guard.siteIndexElse() == arms[1]) {
                return guard;
            }
        }
        return null;
    }

    private BoundaryComparisons() {}
}
