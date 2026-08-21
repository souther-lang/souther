package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputReads;

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
 * <p>Asked of a comparison and answered for a whole body, which is the shape the question has.
 * Asked of a fork instead, the reader of lines had to find a fork before it could find a rule — so
 * widening what bears a line would have meant rewriting that reader rather than this, and a
 * comparison given a name a line above the fork that tests it stands under no fork to be found from.
 *
 * <p>What the policy is today: a comparison written in the condition of a fork whose arms a run can
 * be recorded in, reached through {@code &&} and {@code ||}. So a comparison given a name a line
 * above the fork draws no line, and neither does one returned as the answer or handed to a
 * combinator — which are comparisons the catalog holds, the numbering numbers and the reading names.
 * Widening that is a change to what the rules of a model divide rather than to what a body is read
 * as, and it is a change here.
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
     * One comparison a line may be drawn on, and where the names in it point.
     *
     * <p>The reading travels with the comparison because it is not the same at every one of them: a
     * comparison inside an expanded helper is about the argument the call handed it, and read
     * against the names outside the binding it is about nothing at all.
     */
    record Bearing(Core.Binary comparison, InputReads reads) {}

    private final List<Bearing> bearing;

    private BoundaryComparisons(List<Bearing> bearing) {
        this.bearing = List.copyOf(bearing);
    }

    /** The comparisons a line may be drawn on, in the order the source wrote them. */
    List<Bearing> all() {
        return bearing;
    }

    /** The comparisons of {@code body} a line may be drawn on. */
    static BoundaryComparisons of(Core body, CoverageSites.Plan plan, InputReads reads) {
        List<Bearing> bearing = new ArrayList<>();
        gather(body, plan, reads, bearing);
        return new BoundaryComparisons(bearing);
    }

    private static void gather(Core e, CoverageSites.Plan plan, InputReads reads,
                               List<Bearing> bearing) {
        // A fork no run can be recorded in is one no line drawn under it could ever be shown met, so
        // the rules there are read and nothing is owed.
        if (e instanceof Core.If iff && guardOf(plan, iff) != null) {
            inTheCondition(Condition.of(iff.cond(), reads), plan, bearing);
        }
        // Inside what a `let` binds, since that is where a name standing for an argument is read as
        // the argument. What a binding inside a condition contributes is {@link Condition}'s to
        // look through; this is the one above the fork.
        InputReads inside = e instanceof Core.LetIn let ? reads.and(let.binder(), let.value())
                : reads;
        Core.forEachChild(e, child -> gather(child, plan, inside, bearing));
    }

    /**
     * The comparisons one condition is built out of.
     *
     * <p>Read off {@link Condition} and not off the shape of the node, which is where every reader
     * of a condition used to decide for itself which shapes combine, which are transparent and
     * which are something to say about.
     *
     * <p>The ones the plan numbered, which is not all of them. Meeting a line takes getting the
     * comparison to answer, and whether it answered is what a site records — so a comparison with no
     * site is one no row could ever be shown to have reached, and a border drawn on it would owe a
     * row nothing can measure.
     */
    private static void inTheCondition(Condition e, CoverageSites.Plan plan,
                                       List<Bearing> bearing) {
        switch (e) {
            case Condition.Both both -> {
                inTheCondition(both.left(), plan, bearing);
                inTheCondition(both.right(), plan, bearing);
            }
            case Condition.Either either -> {
                inTheCondition(either.left(), plan, bearing);
                inTheCondition(either.right(), plan, bearing);
            }
            case Condition.Compares one -> {
                if (plan.comparisonAt(one.at()).isPresent()) {
                    bearing.add(new Bearing(one.at(), one.reads()));
                }
            }
            case Condition.NotRead ignored -> { }
        }
    }

    /** The arms a row that reached this fork's condition can be recorded in, or null where none
     *  can. */
    private static CoverageSites.GuardRef guardOf(CoverageSites.Plan plan, Core.If iff) {
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
}
