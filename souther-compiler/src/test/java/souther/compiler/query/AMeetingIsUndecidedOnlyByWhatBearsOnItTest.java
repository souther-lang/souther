package souther.compiler.query;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.regex.PatternPlan;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A meeting is left undecided by what bears on it, and a behavior is left partial by anything.
 *
 * <p>Two axes, and one answer used to serve both. Whether the measurement of a behavior was made in
 * full is a question about all of it: a group the walk would not take leaves it short, whatever else
 * was read. Whether one meeting is a gap is a question about that meeting: a group nobody walked
 * bears on it only where that group could have stated it, and a group over other decisions could
 * not have.
 *
 * <p>Run together, the second becomes the first — one wide group would leave every meeting of every
 * other group undecided, and a gap the rows established and nothing can take away would be reported
 * as one nobody could decide, with no row offered for it. Souther's account already holds the two
 * apart everywhere else: a point of a border answers for its own readings while the module it is in
 * says what every measure of it went without.
 */
class AMeetingIsUndecidedOnlyByWhatBearsOnItTest {

    /**
     * Two meetings over different decisions, one of them wider than the measure will walk.
     *
     * <p>The charge is settled by the total, the membership and the delivery; the cover by the
     * insurance and the delivery. Neither states the other's requirements: the cover's are over
     * decisions the charge's group has no outcome for.
     */
    private static final String APART = """
            module example.apart

            data Total = Int
            data Premium
            data Standard
            data Membership = Premium | Standard
            data Express
            data Regular
            data Delivery = Express | Regular
            data Yes
            data No
            data Insured = Yes | No
            data Fee = { charge: Int, cover: Int }

            behavior shippingFee : (total: Total, member: Membership, delivery: Delivery,
                                    insured: Insured) -> Fee
                constructs Fee

            let shippingFee (total, member, delivery, insured) = Fee {
                charge = baseFee(total, member) + expressFee(delivery),
                cover = coverFee(insured) + expressFee(delivery)
            }

            let baseFee (total: Total, member: Membership): Int =
                match member with
                    | Premium -> 0
                    | Standard -> if total.value >= 5000 then 0 else 500

            let expressFee (delivery: Delivery): Int =
                match delivery with
                    | Express -> 500
                    | Regular -> 0

            let coverFee (insured: Insured): Int =
                match insured with
                    | Yes -> 100
                    | No -> 0

            example shippingFee
                | (Total(0), Premium, Express, Yes)  -> Fee { charge = 500, cover = 600 }
                | (Total(0), Standard, Regular, No)  -> Fee { charge = 500, cover = 0 }
            """;

    /**
     * The behavior is short of a measurement, and the meetings the walk did read are still gaps.
     *
     * <p>Both in one test, because the point is that they hold at once. Either alone is satisfied
     * by the answer this is here to rule out: a run that reported nothing would have the first, and
     * one that called itself whole would have the second.
     */
    @Test
    void aWideGroupLeavesTheBehaviorPartialAndTheOtherGroupsGapsDecided() {
        AdequacyReport.BehaviorReport behavior = behaviorUnder(5);

        assertFalse(behavior.evidence().interaction().asked().notMeasured().isEmpty(),
                "one group is wider than this walks");
        assertEquals(MeasurementStatus.PARTIAL, behavior.status(),
                () -> "so the behavior is short of a measurement: " + behavior.weakenedBy());

        List<Adequacy.Finding> gaps = behavior.findings().stream()
                .filter(each -> each.kind() == Adequacy.Kind.INTERACTION_UNCOVERED)
                .toList();
        assertFalse(gaps.isEmpty(), "the group it did walk leaves combinations unmade");
        assertEquals(List.of(), gaps.stream()
                        .filter(each -> !each.weakenedBy().isEmpty())
                        .map(each -> each.about().toString())
                        .toList(),
                "and a group over other decisions could not have made any of them");
    }

    /** And a build refuses over them, which is what being decided is for. */
    @Test
    void aBuildMayRefuseOverAGapTheWalkedGroupEstablished() {
        assertTrue(AdequacyReport.of(compiled(5)).adequacyGaps().stream()
                        .anyMatch(each -> each.kind() == Adequacy.Kind.INTERACTION_UNCOVERED),
                "a combination the rows leave unmade is one a strict build may refuse over");
    }

    private static AdequacyReport.BehaviorReport behaviorUnder(int cellsPerGroup) {
        List<AdequacyReport.BehaviorReport> behaviors =
                AdequacyReport.of(compiled(cellsPerGroup)).modules().getFirst().behaviors();
        assertEquals(1, behaviors.size(), "one behavior in the model");
        return behaviors.getFirst();
    }

    private static Compilation compiled(int cellsPerGroup) {
        Compilation compilation = Compilation.ofSource(APART, "Main")
                .withAdequacyPolicy(new AdequacyPolicy(
                        new AdequacyPolicy.OfTheMeasures(Budgets.measures().pairSpace(),
                                cellsPerGroup, PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS),
                        Budgets.generation()));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        return compilation;
    }
}
