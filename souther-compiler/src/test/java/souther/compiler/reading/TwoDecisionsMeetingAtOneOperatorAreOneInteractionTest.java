package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
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
 *
 * <p>The helpers below are written with parameter names of their own, on purpose. A helper is
 * spliced into the body that calls it and binds the call's argument to its own parameter, so a
 * reading that took the word rather than the position would say about one parameter of the behavior
 * what is true of another — and would be right here only for as long as the two were spelled alike.
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

            let baseFee (spend: Total, tier: Membership): Int =
                match tier with
                    | Premium -> 0
                    | Standard -> if spend.value >= 5000 then 0 else 500

            let expressFee (speed: Delivery): Int =
                match speed with
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

    /** The same two charges, named by `let` rather than by a helper the inliner splices in. */
    private static final String BOUND = """
            module example.bound

            data Membership = Premium | Standard
            data Delivery = Express | Regular

            behavior fee : (member: Membership, delivery: Delivery) -> Int

            let fee (member, delivery) = {
                let base = match member with
                    | Premium -> 0
                    | Standard -> 500
                let express = match delivery with
                    | Express -> 500
                    | Regular -> 0

                base + express
            }
            """;

    /** Two decisions on plain Bool inputs, read as conditions rather than compared. */
    private static final String FLAGS = """
            module example.flags

            behavior fee : (member: Bool, express: Bool) -> Int

            let fee (member, express) =
                (if member then 0 else 500) + (if express then 500 else 0)
            """;

    /**
     * Two helpers whose parameters are spelled as the behavior's, and handed the other one's
     * argument. Whichever word a reading takes, it is the wrong position.
     */
    private static final String CROSSED = """
            module example.crossed

            data Membership = Premium | Standard

            behavior fee : (member: Membership, other: Membership) -> Int

            let base (member: Membership): Int =
                match member with
                    | Premium -> 0
                    | Standard -> 500

            let extra (other: Membership): Int =
                match other with
                    | Premium -> 10
                    | Standard -> 20

            let fee (member, other) = base(other) + extra(member)
            """;

    private static List<Interaction> read(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        return CoverageRead.of(behavior, body,
                checked.plan(), inputs, rules).interactions();
    }

    /** The sizes of each group's factors, which is the shape of the space a row is owed for. */
    private static List<List<Integer>> shape(List<Interaction> found) {
        return found.stream()
                .map(group -> group.factors().stream().map(f -> f.outcomes().size()).toList())
                .toList();
    }

    /**
     * The charge is the sum of two decisions, so the two are one group — and the base charge is one
     * factor of three outcomes rather than two factors, because the comparison on the total is a
     * decision only where the member is Standard.
     */
    @Test
    void aSumOfTwoDecisionsIsOneGroupOfTwoFactors() {
        assertEquals(List.of(List.of(3, 2)), shape(read(SHIPPING, "shippingFee")),
                "the base charge is settled three ways and the express charge two");
    }

    /** Two fields of one record are not a meeting, so nothing groups them. */
    @Test
    void twoDecisionsWritingTwoFieldsAreNotAGroup() {
        assertEquals(List.of(), read(APART, "describe"),
                "a constructor is where two values arrive, not where one is made of them");
    }

    @Test
    void twoDecisionsNamedByLetAreStillOneGroup() {
        assertEquals(List.of(List.of(2, 2)), shape(read(BOUND, "fee")),
                "naming a decision does not stop it being one");
    }

    @Test
    void aDecisionOnABoolInputIsSaidOfThatInput() {
        List<Interaction> found = read(FLAGS, "fee");
        assertEquals(1, found.size(), "the two charges meet once: " + found);
        assertEquals("member=true",
                found.get(0).factors().get(0).outcomes().get(0).holds().get(0).toString(),
                "a condition that is the input says so: " + found);
    }

    /**
     * A decision is about the position the argument names, not about the word the helper binds it
     * under. Both helpers here match a parameter of their own called after a parameter of the
     * behavior, and each is handed the other one's.
     */
    @Test
    void aDecisionIsAboutThePositionAndNotTheNameItIsReachedUnder() {
        List<Interaction> found = read(CROSSED, "fee");
        assertEquals(1, found.size(), "the two charges meet once: " + found);
        assertEquals(List.of("other=Premium", "member=Premium"),
                found.get(0).factors().stream()
                        .map(factor -> factor.outcomes().get(0).holds().get(0).toString())
                        .toList(),
                "the first charge is about `other` and the second about `member`: " + found);
    }

    /** Three decisions summed, which the tree holds as one operator applied twice. */
    private static final String THREE = """
            module example.three

            data Tier = Bronze | Silver

            behavior fee : (a: Tier, b: Tier, c: Tier) -> Int

            let rate (tier: Tier): Int =
                match tier with
                    | Bronze -> 0
                    | Silver -> 1

            let fee (a, b, c) = rate(a) + rate(b) + rate(c)
            """;

    /**
     * A run of one operator is one meeting of all its values. Read as two, the inner one asks for
     * the product of the first two decisions and the outer asks for that product against the third
     * — so every row the inner wants is a row the outer already wanted, offered again under a name
     * that fixes less.
     */
    @Test
    void aRunOfOneOperatorIsOneGroupOfAllItsValues() {
        assertEquals(List.of(List.of(2, 2, 2)), shape(read(THREE, "fee")),
                "three decisions making one number are three factors of one group");
    }

    /** Three decisions joined by an operator that stops as soon as the answer is settled. */
    private static final String SHORT_CIRCUIT = """
            module example.shortcircuit

            behavior pick : (a: Bool, b: Bool, c: Bool) -> Bool

            let pick (a, b, c) =
                (if a then true else false)
                    && (if b then true else false)
                    && (if c then true else false)
            """;

    /** A charge one of whose arms answers nothing and aborts instead. */
    private static final String ABORTING = """
            module example.aborting

            data Choice = A | B
            data Other = C | D

            behavior fee : (choice: Choice, other: Other) -> Int

            let fee (choice, other) = {
                let left = match choice with
                    | A -> 100
                    | B -> unreachable "a B never reaches this charge"
                let right = match other with
                    | C -> 10
                    | D -> 20

                left + right
            }
            """;

    /**
     * An operator that stops as soon as the answer is settled does not consume both sides. Read as
     * a meeting it asks for the combinations of decisions the short circuit never reaches: nothing
     * evaluates the second condition on a path the first settled, so a cell naming both is a cell
     * the body has no path to.
     */
    @Test
    void anOperatorThatStopsEarlyIsNotAMeetingOfBothItsSides() {
        assertEquals(List.of(), read(SHORT_CIRCUIT, "pick"),
                "the second side is not evaluated on every path the first leaves");
    }

    /**
     * An arm that answers nothing is not a way the value is settled. Counted as one, the charge on
     * the left would vary two ways where it varies one, and the group would ask for a row at a
     * combination whose left half aborts before the sum is reached.
     */
    @Test
    void anArmThatAnswersNothingIsNotAWayTheValueIsSettled() {
        assertEquals(List.of(), read(ABORTING, "fee"),
                "one of the two arms answers a value, so the left charge is not a factor");
    }

    /** Three decisions summed inside an arm, where the arm around them settles what it settles. */
    private static final String INSIDE_AN_ARM = """
            module example.arm

            data Choice = A | B

            behavior fee : (choice: Choice, a: Bool, b: Bool, c: Bool) -> Int

            let fee (choice, a, b, c) =
                match choice with
                    | A -> 0
                    | B -> {
                        let counted =
                            (if a then 1 else 0)
                            + (if b then 1 else 0)
                            + (if c then 1 else 0)

                        ANSWER
                    }
            """;

    /** The arm the decisions are in answers a value, so what is inside it is read. */
    @Test
    void whatIsInsideAnArmThatAnswersIsRead() {
        assertEquals(List.of(List.of(2, 2, 2)),
                shape(read(INSIDE_AN_ARM.replace("ANSWER", "counted"), "fee")),
                "the three decisions make the value the arm answers with");
    }

    /**
     * The same decisions in an arm that answers nothing are not read. They are made and thrown away
     * with the run that aborts, so no row observes what they came to — and a group found in there
     * would be offered rows that settle nothing, out of the budget the rest of them share.
     */
    @Test
    void whatIsInsideAnArmThatAnswersNothingIsNotRead() {
        assertEquals(List.of(),
                read(INSIDE_AN_ARM.replace("ANSWER", "unreachable \"an A is the only answer\""), "fee"),
                "nothing arrives at a value down there");
    }

    /** Two decisions each written under one gate, and summed. */
    private static final String GATED = """
            module example.gated

            behavior fee : (gate: Bool, a: Bool, b: Bool) -> Int

            let fee (gate, a, b) = {
                let left = if gate then (if a then 10 else 20) else 0
                let right = if gate then (if b then 100 else 200) else 0

                left + right
            }
            """;

    /**
     * A meeting inside an arm is reached only by a row that takes that arm, and the group says so.
     *
     * <p>Without it a row offered for one of these combinations may go the other way round the fork
     * and never reach the operator, and a row already written over there reads as one that covers
     * the combination. What varies together is half of what a group is; the other half is what it
     * takes to get to where they vary.
     */
    @Test
    void aGroupCarriesWhatItTakesToReachIt() {
        List<Interaction> found = read(INSIDE_AN_ARM.replace("ANSWER", "counted"), "fee");

        assertEquals(1, found.size(), "the three decisions meet once: " + found);
        assertEquals(List.of("choice=B"),
                found.get(0).reach().stream().map(Object::toString).toList(),
                "and are reached by the arm they are written in: " + found);
    }

    /**
     * Two factors written under one gate are still two factors. The gate is in the outcomes of
     * both, so the choices that put it two ways are not combinations, and the ones left are the
     * four inside the gate and the one outside it.
     */
    @Test
    void twoFactorsUnderOneGateAreStillAGroup() {
        assertEquals(List.of(List.of(3, 3)), shape(read(GATED, "fee")),
                "each side is settled by the gate and then by its own decision");
    }

    /** Two decisions inside a function the body makes and calls somewhere else. */
    private static final String LAMBDA = """
            module example.lambda

            behavior fee : (gate: Bool, a: Bool, b: Bool) -> Int

            let fee (gate, a, b) = {
                let f: (Int) -> Int = (x) -> (if a then 1 else 0) + (if b then 10 else 20)

                if gate then f(0) else 0
            }
            """;

    /**
     * A function a body names is read where it is called, under what it takes to get to the call.
     *
     * <p>Which is the whole of the question the fork above the call raises. The decisions are in a
     * function made before the fork, and a reading that took them where the function was made would
     * carry no way in at all — a row varying the two while the call never happens would be offered
     * for the group. Read where the call is, the way in is the call's.
     */
    @Test
    void aFunctionsDecisionsAreReadWhereItIsCalledFrom() {
        List<Interaction> found = read(LAMBDA, "fee");

        assertEquals(List.of(List.of(2, 2)), shape(found), "the two decisions meet once: " + found);
        assertEquals(List.of("gate=true"),
                found.get(0).reach().stream().map(Object::toString).toList(),
                "under what it takes to reach the call: " + found);
    }
}
