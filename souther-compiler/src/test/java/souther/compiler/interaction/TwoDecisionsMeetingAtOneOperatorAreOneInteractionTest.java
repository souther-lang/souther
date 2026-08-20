package souther.compiler.interaction;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Which decisions of a body determine one value together, read off the body.
 *
 * <p>Meeting is what makes an interaction, and a node with several children is not on its own a
 * meeting: two decisions writing two fields of one record arrive at a constructor and no
 * observation is a function of both. What forms a group is two of them being consumed into one
 * value — the operands of an arithmetic operator or a comparison, the arguments of a call that
 * answers one value — so the reading is over what a value is made of and not over the shape of
 * the tree above it.
 */
class TwoDecisionsMeetingAtOneOperatorAreOneInteractionTest {

    private static final String SHIPPING = """
            module example.shipping

            data Total = Int
                invariant value >= 0
                invariant value <= 1000000

            data Membership = Premium | Standard

            data Delivery = Express | Regular

            data Fee = Int
                invariant value >= 0

            behavior shippingFee : (total: Total, member: Membership, delivery: Delivery) -> Fee
                constructs Fee

            let baseFee (total: Total, member: Membership): Int =
                match member with
                    | Premium -> 0
                    | Standard -> if total.value >= 5000 then 0 else 500

            let expressFee (delivery: Delivery): Int =
                match delivery with
                    | Express -> 500
                    | Regular -> 0

            let shippingFee (total, member, delivery) =
                Fee(baseFee(total, member) + expressFee(delivery))
            """;

    /** Two decisions, one written per field, that no observation is a function of both of. */
    private static final String APART = """
            module example.apart

            data Order = { price: Int, message: String }

            behavior describe : (urgent: Bool, paid: Bool) -> Order
                constructs Order

            let describe (urgent, paid) =
                Order { price = if paid then 100 else 200
                      , message = if urgent then "now" else "later"
                      }
            """;

    private static List<Interaction> read(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies());
        return Interactions.of(behavior, body, plan);
    }

    /**
     * The charge is the sum of two decisions, so the two are one group — and the base charge is one
     * factor of three outcomes rather than two factors, because the comparison on the total is a
     * decision only where the member is Standard.
     */
    @Test
    void aSumOfTwoDecisionsIsOneGroupOfTwoFactors() {
        List<Interaction> found = read(SHIPPING, "shippingFee");

        assertEquals(1, found.size(), "the two charges meet once: " + found);
        List<Integer> sizes = found.get(0).factors().stream().map(f -> f.outcomes().size()).toList();
        assertEquals(List.of(3, 2), sizes,
                "the base charge is settled three ways and the express charge two: " + found);
    }

    /** Two fields of one record are not a meeting, so nothing groups them. */
    @Test
    void twoDecisionsWritingTwoFieldsAreNotAGroup() {
        assertEquals(List.of(), read(APART, "describe"),
                "a constructor is where two values arrive, not where one is made of them");
    }
}
