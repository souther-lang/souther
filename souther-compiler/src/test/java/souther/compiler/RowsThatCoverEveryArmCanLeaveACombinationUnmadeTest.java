package souther.compiler;

import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.CombinationCriterion;
import souther.compiler.query.Compilation;
import souther.compiler.query.InteractionEvidence;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Rows that go through every arm of a body can still leave two of its decisions never both live.
 *
 * <p>The charge below is the sum of two decisions: a base charge settled three ways and an express
 * charge settled two. Four rows reach every arm and every rule of it, and none of them makes both
 * charges non-zero — so the only answer both decisions take part in is never produced, and an
 * implementation taking the larger of the two instead of their sum holds against all four.
 *
 * <p>What this pins is that the measure says so. The rows are what a reader would write from the
 * arms and the classes, and the combinations the body has are what is left over.
 *
 * <p>Built here rather than left to the corpus. No model the corpus carries brings two decisions
 * together at one value, so the snapshots would go on matching whatever this measure came to.
 */
class RowsThatCoverEveryArmCanLeaveACombinationUnmadeTest {

    private static final String MODEL = """
            module example.shipping

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
            """;

    /** The four rows a reader writes from the classes: one per pairing, every arm taken. */
    private static final String EVERY_ARM = """

            example shippingFee
                | (Total(0), Premium, Express)     -> Fee(500)
                | (Total(0), Standard, Regular)    -> Fee(500)
                | (Total(5000), Premium, Regular)  -> Fee(0)
                | (Total(5000), Standard, Express) -> Fee(500)
            """;

    /** And the row that makes both charges live at once. */
    private static final String BOTH_LIVE = """
                | (Total(1000), Standard, Express) -> Fee(1000)
            """;

    /**
     * The body has six combinations, and four rows through every arm make four of them.
     *
     * <p>The two left are the ones where the base charge is settled by the comparison and the
     * express charge the other way from the row that already made it. One of them is the row that
     * tells a sum from a maximum.
     */
    @Test
    void rowsThroughEveryArmLeaveTwoOfTheSixCombinationsUnmade() {
        InteractionEvidence meetings = meetingsOf(MODEL + EVERY_ARM);

        assertEquals(6, meetings.counted(), "two decisions, three outcomes and two");
        assertEquals(4, meetings.made().made().orElseThrow().met().size(),
                "and the four rows make four of them");
        assertEquals(2, meetings.notMadeByRows().size(),
                "which leaves the two where both charges are live and where neither is");
    }

    /** And every arm of the body is taken by those same rows, which is what makes the point. */
    @Test
    void theSameRowsGoThroughEveryArmOfTheBody() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(MODEL + EVERY_ARM);

        assertEquals(behavior.evidence().branch().arms().counted(),
                behavior.evidence().branch().arms().covered(),
                "every arm of the body has a row through it");
        assertFalse(behavior.evidence().interaction().notMadeByRows().isEmpty(),
                "and combinations of its decisions are still unmade");
    }

    /** A row that makes one of them is seen making it, and the finding for it goes. */
    @Test
    void aRowThatMakesACombinationIsSeenMakingIt() {
        Set<ObligationIdentity.OfACombinationOfDecisions> before =
                Set.copyOf(meetingsOf(MODEL + EVERY_ARM).notMadeByRows());
        Set<ObligationIdentity.OfACombinationOfDecisions> after =
                Set.copyOf(meetingsOf(MODEL + EVERY_ARM + BOTH_LIVE).notMadeByRows());

        assertEquals(1, after.size(), "the row makes one of the two that were unmade");
        assertTrue(before.containsAll(after), "and leaves the other where it was");
    }

    /**
     * A behavior whose decisions meet is held to them and not to the pair space.
     *
     * <p>The criterion is one or the other, and it is the model that says which.
     */
    @Test
    void aBodyWhoseDecisionsMeetIsHeldToTheCombinationsAndNotToThePairs() {
        assertInstanceOf(CombinationCriterion.Interactions.class,
                behaviorOf(MODEL + EVERY_ARM).evidence().combinations());
    }

    private static InteractionEvidence meetingsOf(String model) {
        return behaviorOf(model).evidence().interaction();
    }

    private static AdequacyReport.BehaviorReport behaviorOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<AdequacyReport.BehaviorReport> behaviors =
                AdequacyReport.of(compilation).modules().getFirst().behaviors();
        assertEquals(1, behaviors.size(), "one behavior in the model");
        return behaviors.getFirst();
    }
}
