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
 */
final class BoundaryComparisons {

    /** One comparison a line may be drawn on, and which arms of the fork prove it was evaluated. */
    record Placed(Core.Binary comparison, OriginRef.GuardOrigin.Witness witness) {}

    /**
     * The comparisons of {@code iff}'s condition, each with what its own place leaves as evidence.
     *
     * <p>Asked per comparison and not per condition. A condition that is nothing but {@code &&}
     * settles it for every operand at once, and so does one that is nothing but {@code ||}; a
     * condition made of both does not. In {@code A && (B || C)} the arm where the whole thing held
     * proves {@code A} was true and so proves {@code B} ran, while {@code C} ran only where
     * {@code B} was false — which is a difference between two operands of one condition, and a
     * single verdict over the whole cannot hold it.
     *
     * <p>Two facts are carried down, and they are not the same one. Whether this subtree is
     * evaluated at all on a given arm, and whether reaching that arm forces the subtree's own value
     * — because it is the second that says whether the operand to its left was true, which is what
     * decides whether the operand to its right ran.
     */
    static List<Placed> of(Core.If iff, ComparisonCatalog catalog) {
        List<Placed> out = new ArrayList<>();
        // At the top there is nothing above to have stopped the condition, and the arm taken is the
        // condition's own value.
        placed(iff.cond(), new Reached(true, true, true, true), catalog, out);
        return out;
    }

    /**
     * What reaching each arm of the enclosing {@code if} says about one subtree of its condition.
     *
     * <p>Four answers and not six, on a premise worth stating rather than leaving to be rediscovered.
     * A subtree can be forced true only where the whole condition is true and forced false only where
     * it is false — {@code &&} passes a true value down to both operands, {@code ||} passes a false
     * one, and neither passes anything the other way. So "false on {@code then}" and "true on
     * {@code else}" are unreachable and are not carried.
     *
     * <p>What makes that hold is that a condition is built from {@code &&} and {@code ||} and
     * nothing else. There is no negation operator: {@code Bool.not} is a helper, inlined to an
     * {@code if} whose condition is the comparison itself, so it never stands between a comparison
     * and the arms this is about. An operator that inverted a value inside a condition would break
     * the premise and want the other two answers, and would find this comment rather than a wrong
     * result.
     *
     * @param onThen    whether reaching the {@code then} arm implies this subtree was evaluated
     * @param onElse    the same for {@code else}
     * @param trueThen  whether reaching {@code then} implies this subtree's own value was true
     * @param falseElse whether reaching {@code else} implies its own value was false
     */
    private record Reached(boolean onThen, boolean onElse, boolean trueThen, boolean falseElse) {

        OriginRef.GuardOrigin.Witness witness() {
            if (onThen && onElse) {
                return OriginRef.GuardOrigin.Witness.BOTH;
            }
            if (onThen) {
                return OriginRef.GuardOrigin.Witness.THEN;
            }
            return onElse ? OriginRef.GuardOrigin.Witness.ELSE
                    : OriginRef.GuardOrigin.Witness.NEITHER;
        }
    }

    private static void placed(Core e, Reached reached, ComparisonCatalog catalog,
                               List<Placed> out) {
        if (e instanceof Core.Binary binary
                && (binary.op() == Hir.BinOp.AND || binary.op() == Hir.BinOp.OR)) {
            boolean and = binary.op() == Hir.BinOp.AND;
            // A conjunction's value being true makes both its operands true; a disjunction's being
            // false makes both false. Neither says anything the other way round.
            Reached left = new Reached(reached.onThen(), reached.onElse(),
                    and && reached.trueThen(), !and && reached.falseElse());
            // The right operand runs where the left settled nothing — which is where the left was
            // true under `&&` and false under `||`, and that is what the left's own forced value
            // above says.
            Reached right = new Reached(
                    and && reached.onThen() && reached.trueThen(),
                    !and && reached.onElse() && reached.falseElse(),
                    and && reached.trueThen(), !and && reached.falseElse());
            placed(binary.left(), left, catalog, out);
            placed(binary.right(), right, catalog, out);
            return;
        }
        // Whether this is a comparison is the catalog's answer. Read off the node's own shape here,
        // this was a second account of what a comparison is — spelled as "a binary that is not
        // `&&` or `||`", which is every arithmetic node in the condition as well.
        catalog.at(e).ifPresent(comparison ->
                out.add(new Placed(comparison.node(), reached.witness())));
    }

    /**
     * The arms a row that reached this fork's condition can be recorded in, or null where none can.
     *
     * <p>What a line drawn here is met by is the comparison having answered, and this is what says
     * which class of the partition a row that got there landed in.
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
