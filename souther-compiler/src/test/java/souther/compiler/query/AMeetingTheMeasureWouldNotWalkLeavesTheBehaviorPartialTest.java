package souther.compiler.query;

import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.MeasurementStatus;
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
 * A meeting the measure would not walk leaves the behavior short of a measurement, and says so.
 *
 * <p>Which combinations of a body's decisions the rows make is a measure of that behavior like the
 * arms and the classes, and what a measure went without is what the behavior went without. A group
 * held back by a limit is exactly that: the combinations were never enumerated, so nothing is owed
 * at any of them — and a behavior that came back whole would be telling a reader that a measurement
 * nobody made found nothing.
 *
 * <p>Both halves, because each fails on its own. The shortfall has to be recorded on the measure,
 * and the measure has to be one of the parts a behavior is read to be made of — a measure recorded
 * perfectly and left out of that list reaches the status, the verdict and the document alike, which
 * is to say it reaches none of them.
 */
class AMeetingTheMeasureWouldNotWalkLeavesTheBehaviorPartialTest {

    /** Two decisions meeting at one value, with six combinations between them. */
    private static final String MODEL = """
            module example.held

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
                | (Total(5000), Premium, Regular)  -> Fee(0)
                | (Total(5000), Standard, Express) -> Fee(500)
            """;

    /**
     * At one combination per group, the group is not walked and the behavior is not whole.
     *
     * <p>It is still held to the combinations of its decisions. Which criterion a behavior is
     * measured against is a question about the body, and a limit is a question about this run — so
     * a group too wide to walk leaves the criterion where the model put it rather than falling back
     * to the pair space.
     */
    @Test
    void aBehaviorWhoseGroupWentUnwalkedIsNotComplete() {
        AdequacyReport.BehaviorReport narrow = behaviorUnder(1);

        assertInstanceOf(CombinationCriterion.Interactions.class, narrow.evidence().combinations(),
                "the body's decisions meet, whatever this run could afford to walk");
        assertEquals(List.of(), narrow.reported().stream()
                        .filter(each -> each.finding().kind() == Adequacy.Kind.PAIR_UNCOVERED)
                        .toList(),
                "nothing is owed at a combination of two classes: that is the other criterion");
        assertFalse(narrow.evidence().interaction().asked().notMeasured().isEmpty(),
                "the group is one the walk would not take");
        assertEquals(MeasurementStatus.PARTIAL, narrow.status(),
                () -> "so the behavior is short of a measurement: " + narrow.weakenedBy());
        assertTrue(narrow.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsNotWalked.class::isInstance),
                () -> "and what it went without says which walk: " + narrow.weakenedBy());
    }

    /** And nothing is owed at a combination of a group nobody walked. */
    @Test
    void nothingIsOwedAtACombinationOfAGroupNobodyWalked() {
        assertEquals(List.of(), AdequacyReport.of(compiled(1)).adequacyGaps().stream()
                        .filter(each -> each.kind() == Adequacy.Kind.INTERACTION_UNCOVERED)
                        .map(each -> each.about().toString())
                        .toList(),
                "a combination nothing enumerated is not one no row makes");
    }

    /** Walked, the same model is whole and says what the rows left unmade. */
    @Test
    void theSameModelWalkedIsWholeAndNamesWhatIsLeft() {
        AdequacyReport.BehaviorReport wide = behaviorUnder(Budgets.measures().cellsPerGroup());

        assertTrue(wide.evidence().interaction().asked().notMeasured().isEmpty(),
                "every group is walked here");
        assertEquals(MeasurementStatus.COMPLETE, wide.status(),
                () -> "so nothing about the meetings is left open: " + wide.weakenedBy());
        assertFalse(wide.evidence().interaction().notMadeByRows().isEmpty(),
                "and the combinations the rows leave unmade are named");
    }

    private static AdequacyReport.BehaviorReport behaviorUnder(int cellsPerGroup) {
        Compilation compilation = compiled(cellsPerGroup);
        List<AdequacyReport.BehaviorReport> behaviors =
                AdequacyReport.of(compilation).modules().getFirst().behaviors();
        assertEquals(1, behaviors.size(), "one behavior in the model");
        return behaviors.getFirst();
    }

    private static Compilation compiled(int cellsPerGroup) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main")
                .withAdequacyPolicy(new AdequacyPolicy(
                        new AdequacyPolicy.OfTheMeasures(Budgets.measures().pairSpace(),
                                cellsPerGroup, PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS),
                        Budgets.generation()));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(),
                () -> AdequacyReport.of(compilation)
                        .human(SourceRendering.namedByIdentity(compilation.texts())));
        return compilation;
    }
}
