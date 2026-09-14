package souther.compiler.query;

import souther.compiler.partition.ObligationIdentity;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A finding whose measurement went without something is not asked for in a generation.
 *
 * <p>A proposal is work offered against an obligation the account established as missing. Where the
 * measurement that raised it went without something, what it says is that nothing was <em>seen</em>
 * doing this — a row already in the file may do it, and one nobody could read is exactly the row
 * that would. Offered anyway, a person is handed a line to write that may be the line above the
 * one they are reading.
 *
 * <p>Which is a rule about a plan and not about a kind of finding. It was kept where the rows for
 * the rules of a decision are gathered and nowhere else, so every other kind asked only what shape
 * the finding was — and each kind added since inherited the omission rather than the rule.
 */
class AnObligationNothingEstablishedAsMissingIsNotWorkToOfferTest {

    /**
     * A body with two meetings, one of them wider than the measure will walk.
     *
     * <p>The first sums three outcomes with two and the second two with two, so a limit between
     * them walks one group and holds the other back. What the walked group leaves unmade is
     * reported — and the measurement that reported it is short of the group nobody walked, so a
     * combination it named as unmade is one an unwalked row may already make.
     */
    private static final String MODEL = """
            module example.unread

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

    /** Nothing a measurement went short of is in the plan, whichever kind of thing it names. */
    @Test
    void nothingAMeasurementWentShortOfIsAskedForInThePlan() {
        Map<String, Adequacy.Filling> filled = filling();
        List<Adequacy.Finding> findings =
                compiled().db().ask(new Adequacy.Findings("example.unread")).value();
        assertFalse(findings == null || findings.isEmpty(), "this model has findings");

        List<String> offeredAnyway = new ArrayList<>();
        for (Adequacy.Finding finding : findings) {
            if (finding.weakenedBy().isEmpty() || !finding.kind().isAboutAnObligation()) {
                continue;
            }
            souther.compiler.partition.GenerationPlan plan =
                    filled.get("shippingFee") == null ? null
                            : filled.get("shippingFee").composed().plan();
            if (plan != null && namedIn(plan, finding)) {
                offeredAnyway.add(finding.about().toString());
            }
        }
        assertEquals(List.of(), offeredAnyway,
                "a row was asked for at something nothing established is missing");
    }

    /** And there is something to have got wrong here, or the walk above says nothing. */
    @Test
    void thisModelHasAFindingAMeasurementWentShortOf() {
        List<Adequacy.Finding> findings =
                compiled().db().ask(new Adequacy.Findings("example.unread")).value();

        assertTrue(findings != null && findings.stream()
                        .anyMatch(each -> !each.weakenedBy().isEmpty()
                                && each.kind().isAboutAnObligation()),
                () -> "nothing here is undecided, so the rule is not exercised: " + findings);
    }

    /** Whether the plan asks for the thing this finding is about. */
    private static boolean namedIn(souther.compiler.partition.GenerationPlan plan,
                                   Adequacy.Finding finding) {
        return switch (finding.about()) {
            case About.ACombinationNoRowMakes(ObligationIdentity.OfACombinationOfDecisions it) ->
                    plan.meetingsOwed().contains(it);
            case About.ACombinationOfTwoClassesNoRowIsIn(
                    ObligationIdentity.OfAFallbackPairCell it) -> plan.pairsOwed().contains(it);
            case About.AnArmNoRowGoesThrough(var arm) -> arm.place().probe().isPresent()
                    && plan.armsOwed().stream()
                            .anyMatch(owed -> owed.recordedAt(arm.place().probe().get()));
            default -> false;
        };
    }

    private static Map<String, Adequacy.Filling> filling() {
        Map<String, Adequacy.Filling> filled =
                Adequacy.generatedOf(compiled().db(), "example.unread");
        return filled == null ? Map.of() : filled;
    }

    /** Measured at a limit between the two groups, so that one is walked and one is not. */
    private static Compilation compiled() {
        if (ANSWERED == null) {
            Compilation compilation = Compilation.ofSource(MODEL, "Main")
                    .withAdequacyPolicy(new souther.compiler.partition.AdequacyPolicy(
                            new souther.compiler.partition.AdequacyPolicy.OfTheMeasures(
                                    souther.compiler.partition.Budgets.measures().pairSpace(), 5,
                                    souther.compiler.regex.PatternPlan.Budget
                                            .OF_BEHAVIOR_DISTINCTIONS),
                            souther.compiler.partition.Budgets.generation()));
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            ANSWERED = compilation;
        }
        return ANSWERED;
    }

    private static Compilation ANSWERED;
}
