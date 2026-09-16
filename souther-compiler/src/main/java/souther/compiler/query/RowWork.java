package souther.compiler.query;

import souther.compiler.partition.ClassOfAPosition;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObligationIdentity;

import java.util.List;
import java.util.Set;

/**
 * What a generation would compose rows for, for one behavior.
 *
 * <p>The one statement of it. A block is written from a plan and a rule search, and an editor
 * offering to write that block stands beside the declaration before either has run — so the two used
 * to be two lists of reasons, gathered from the same measures by different walks. The offer asked
 * the findings and the lines; the plan took its classes off the partition measure and its rules off
 * a part of the account the offer never read. A behavior whose only work was the classes was offered
 * nothing and had a block written for it.
 *
 * <p>So this is what the generation is asked for, said once. The plan is built from it, the rule
 * search is set from it, and whether an offer stands is whether it holds anything — and a reason
 * added here reaches all three or none.
 *
 * <p><b>What the generation composes for, and not everything a row could settle.</b> A row composed
 * for a class may apply an input case the model states, and the account says so where the rows are
 * read ({@code Adequacy.atCase}); nothing is ever composed for one. Counted here, the offer would
 * stand where the block has nothing, which is the disagreement this exists to remove, pointing the
 * other way.
 *
 * @param classes  one class of one position apiece, off the partition measure's own reading
 * @param arms     the arms of the body nothing reaches, each with every place a run through it is
 *                 recorded at
 * @param pairs    the combinations of two classes no row sits in, where the pair space is what the
 *                 behavior is held to
 * @param meetings the combinations of the body's decisions no row makes
 * @param rules    the ways through the body no row takes
 * @param points   the points of the lines this behavior's rules and its declarations' draw that are
 *                 worth looking for a row at, and that this module answers for
 */
public record RowWork(List<ClassOfAPosition> classes, List<Generator.ArmOwed> arms,
                      List<ObligationIdentity.OfAFallbackPairCell> pairs,
                      List<ObligationIdentity.OfACombinationOfDecisions> meetings,
                      Set<DecisionRule> rules,
                      List<BorderObligationPointAssessment> points) {

    /** Nothing at all, which is what a behavior no row is owed for comes to. */
    public static final RowWork NONE = new RowWork(List.of(), List.of(), List.of(), List.of(),
            Set.of(), List.of());

    public RowWork {
        classes = List.copyOf(classes);
        arms = List.copyOf(arms);
        pairs = List.copyOf(pairs);
        meetings = List.copyOf(meetings);
        rules = Set.copyOf(rules);
        points = List.copyOf(points);
    }

    /**
     * Whether a generation asked for this would look for anything.
     *
     * <p>Every part, because each of them is a row somebody would be handed. Asked of one of them,
     * a surface would be deciding which kinds of work are worth telling an author about — which is
     * the decision this type exists to take away from its readers.
     */
    public boolean isEmpty() {
        return classes.isEmpty() && arms.isEmpty() && pairs.isEmpty() && meetings.isEmpty()
                && rules.isEmpty() && points.isEmpty();
    }
}
