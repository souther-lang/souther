package souther.compiler.query;

import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
 * <p>A limit on the measure's walk is held in
 * {@link AMeetingTheMeasureWouldNotWalkLeavesTheBehaviorPartialTest}; a limit on what a generation
 * may write is held here.
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
     * Lowering what a generation may write changes what is offered, not what is owed.
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
