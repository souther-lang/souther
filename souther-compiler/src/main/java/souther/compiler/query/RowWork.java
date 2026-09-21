package souther.compiler.query;

import souther.compiler.partition.ClassOfAPosition;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObligationIdentity;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;

/**
 * Why a generation of one behavior would be worth making, for a caller that has not made one.
 *
 * <p>The criterion, and the one statement of it. A block is written from a plan, a rule search and
 * a boundary search, and an editor offering to write that block stands beside the declaration
 * before any of them has run — so what is owed used to be gathered twice, from the same measures by
 * different walks. The offer asked the findings and the lines; the plan took its classes off the
 * partition measure and its rules off a part of the account the offer never read. A behavior whose
 * only work was the classes of its position was offered nothing and had a block written for it.
 *
 * <p><b>The criterion and not the algorithm.</b> A search is asked for where this holds something,
 * and what it then composes is its own answer. Four of these are handed to the search as the list
 * it walks ({@link souther.compiler.partition.GenerationPlan}) and the rules are handed to the one
 * that settles them; the points are not handed to anything. What is owed at a line is looked for by
 * a search of its own, which reads the same measurement these were taken from
 * ({@link ObligationAssessment#worthSearching}) and decides for itself where to look — so this says
 * a boundary search is worth making and never which rows come back from one. Driven from here, the
 * offer would have to compose at the moment an editor decides whether to draw a lightbulb, which is
 * what standing in front of the block is for.
 *
 * <p><b>What a generation composes for, and not everything a row could settle.</b> A row composed
 * for a class may apply an input case the model states, and the account says so where the rows are
 * read ({@code Adequacy.atCase}); nothing is ever composed for one. Counted here, the offer would
 * stand where the block has nothing.
 *
 * @param classes  one class of one position apiece, off the partition measure's own reading
 * @param arms     the arms of the body nothing reaches, each with every place a run through it is
 *                 recorded at, keyed on the account identity the finding was raised against — the
 *                 one place that pairing is made, so nothing downstream reads it back off a search
 *                 target and nothing rebuilds it from a second derivation
 * @param pairs    the combinations of two classes no row sits in, where the pair space is what the
 *                 behavior is held to
 * @param meetings the combinations of the body's decisions no row makes
 * @param rules    the ways through the body no row takes, once apiece and in the order the
 *                 measurement's findings name them — the same order the classes, the arms, the
 *                 pairs and the meetings are held in, and the order a person is shown the work in
 * @param points   the points of the lines this behavior's rules and its declarations' draw that are
 *                 worth looking for a row at, and that this module answers for. What is read of
 *                 them is that there are some: the rows at a line are the boundary search's to
 *                 compose
 */
public record RowWork(List<ClassOfAPosition> classes,
                      SequencedMap<ObligationIdentity.OfAnArm, Generator.ArmOwed> arms,
                      List<ObligationIdentity.OfAFallbackPairCell> pairs,
                      List<ObligationIdentity.OfACombinationOfDecisions> meetings,
                      List<DecisionRule> rules,
                      List<BorderObligationPointAssessment> points) {

    /** Nothing at all, which is what a behavior no row is owed for comes to. */
    public static final RowWork NONE = new RowWork(List.of(), new LinkedHashMap<>(), List.of(),
            List.of(), List.of(), List.of());

    public RowWork {
        classes = List.copyOf(classes);
        arms = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(arms));
        pairs = List.copyOf(pairs);
        meetings = List.copyOf(meetings);
        rules = List.copyOf(rules);
        points = List.copyOf(points);
    }

    /**
     * Whether a generation asked about this behavior would look for anything.
     *
     * <p>Every part, because each of them is a search worth making. Asked of one of them, a surface
     * would be deciding which kinds of work are worth telling an author about — which is the
     * decision this type exists to take away from its readers.
     *
     * <p>Empty is what an offer stands on and is not what a block comes to. A search asked for here
     * may compose nothing, which is news about the search and not about this.
     */
    public boolean isEmpty() {
        return classes.isEmpty() && arms.isEmpty() && pairs.isEmpty() && meetings.isEmpty()
                && rules.isEmpty() && points.isEmpty();
    }
}
