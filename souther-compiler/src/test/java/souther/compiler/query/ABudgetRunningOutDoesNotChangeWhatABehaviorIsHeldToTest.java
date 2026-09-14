package souther.compiler.query;

import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.regex.PatternPlan;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A budget that runs out leaves the criterion where the model put it.
 *
 * <p>Which criterion a behavior's combinations are measured against is a question about the body:
 * its decisions meet somewhere, or they do not. A limit is a question about this run. Read off what
 * the measuring came to, a behavior whose group was too wide to walk would come back held to the
 * pair space — a different universe of requirements, a different denominator, and a verdict that
 * moves with a number nobody in the model wrote. That is ADR-0089's criterion switching, arriving
 * as a default rather than as a decision.
 *
 * <p>So both halves are held: what the behavior is held to is the same under a budget that stops
 * the walk, and what the run could not measure is said rather than answered from elsewhere.
 */
class ABudgetRunningOutDoesNotChangeWhatABehaviorIsHeldToTest {

    /** Two decisions meeting at one value: three outcomes and two, so six combinations. */
    private static final String MODEL = """
            module example.budget

            data Total = Int
            data Premium
            data Standard
            data Membership = Premium | Standard
            data Express
            data Regular
            data Delivery = Express | Regular
            data Fee = Int

            behavior shippingFee : (total: Total, member: Membership, delivery: Delivery) -> Fee
                constructs Fee

            let shippingFee (total, member, delivery) =
                Fee(baseFee(total, member) + expressFee(delivery))

            let baseFee (total: Total, member: Membership): Int =
                match member with
                    | Premium -> 0
                    | Standard -> if total.value >= 5000 then 0 else 500

            let expressFee (delivery: Delivery): Int =
                match delivery with
                    | Express -> 500
                    | Regular -> 0

            example shippingFee
                | (Total(0), Premium, Express)     -> Fee(500)
                | (Total(0), Standard, Regular)    -> Fee(500)
            """;

    /**
     * A group too wide for the measure to walk is a group all the same.
     *
     * <p>At one combination per group the walk offers nothing, and the six this body has go
     * uncounted. The behavior is still held to them: the meeting is what the reading found, and
     * whether the measure could afford to walk it is a fact about this run.
     */
    @Test
    void aGroupTheMeasureWouldNotWalkIsStillWhatTheBehaviorIsHeldTo() {
        AdequacyReport.BehaviorReport narrow = behaviorUnder(
                new AdequacyPolicy.OfTheMeasures(Budgets.measures().pairSpace(), 1,
                        PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS),
                Budgets.generation());

        assertInstanceOf(CombinationCriterion.Interactions.class, narrow.evidence().combinations(),
                "the body's decisions meet, whatever this run could afford to walk");
        assertFalse(narrow.evidence().interaction().asked().notMeasured().isEmpty(),
                "and the group the walk would not take is named as one nothing was measured of");
        assertEquals(List.of(), findingsOf(narrow, Adequacy.Kind.PAIR_UNCOVERED),
                "nothing is owed at a combination of two classes: that is the other criterion");
    }

    /**
     * And lowering what a generation may write changes what is offered, not what is owed.
     *
     * <p>A row limit is spent after the requirements are known. The same combinations are unmade
     * under both, and the narrow run says it stopped rather than reporting fewer.
     */
    @Test
    void aRowLimitChangesWhatIsOfferedAndNotWhatIsOwed() {
        AdequacyReport.BehaviorReport wide =
                behaviorUnder(Budgets.measures(), Budgets.generation());
        AdequacyReport.BehaviorReport narrow = behaviorUnder(Budgets.measures(),
                new AdequacyPolicy.OfTheGeneration(1, Budgets.generation().cellsPerGroup()));

        assertInstanceOf(CombinationCriterion.Interactions.class, narrow.evidence().combinations());
        assertEquals(wide.evidence().interaction().notMadeByRows(),
                narrow.evidence().interaction().notMadeByRows(),
                "the combinations no row makes are the body's, and a generation spends after them");
        assertEquals(findingsOf(wide, Adequacy.Kind.INTERACTION_UNCOVERED).size(),
                findingsOf(narrow, Adequacy.Kind.INTERACTION_UNCOVERED).size(),
                "and each of them is still asked for");
        assertTrue(findingsOf(wide, Adequacy.Kind.INTERACTION_UNCOVERED).size() > 1,
                "a model with one gap would pass this whatever the limit did");
    }

    private static List<AdequacyReport.ReportedFinding> findingsOf(
            AdequacyReport.BehaviorReport behavior, Adequacy.Kind kind) {
        return behavior.reported().stream()
                .filter(each -> each.finding().kind() == kind)
                .toList();
    }

    private static AdequacyReport.BehaviorReport behaviorUnder(
            AdequacyPolicy.OfTheMeasures measures, AdequacyPolicy.OfTheGeneration generation) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main")
                .withAdequacyPolicy(new AdequacyPolicy(measures, generation));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<AdequacyReport.BehaviorReport> behaviors =
                AdequacyReport.of(compilation).modules().getFirst().behaviors();
        assertEquals(1, behaviors.size(), "one behavior in the model");
        return behaviors.getFirst();
    }
}
