package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * An operand of an operation a run works out before a comparison is not always a place of the
 * input or a form of places: it is a name a {@code let} or a call binds, a choice between values,
 * or a number read off a value a lookup answers. What the operation may stop a run on is asked of
 * the numbers the operand lies between, and the operand lies between the numbers it was made of: a
 * choice between those of its arms, a name those of what it binds, a number of a newtype those its
 * rules leave it.
 *
 * <p>The behavior relates the sku of each line to the skus of an order, and works out a number of
 * each line before it. A number that stops no run, or one that may stop it only on places apart
 * from the sku, leaves the relation reached at every value
 * ({@code rule_relating_two_values}, as with no number). One that may stop a run on the sku ties
 * it, and the relation is not shown reached at every value of either.
 *
 * <p>Writing the same number through a {@code let} or a call is the same number, so the places
 * it leaves unread are those of the number written out.
 */
class AnOperandThatIsNoInputPlaceCarriesTheRangeItIsMadeOfTest {

    private static final String DECLARATIONS = """
            module probe

            data Qty = Int
                invariant value >= 0 && value <= 1000
            data Price = Int
                invariant value >= 0 && value <= 1000
            data Rate = Decimal
                invariant value > 0.0m
            data Box = { n: Int }
                invariant n >= 0
            data Tray = { n: Int }
                invariant n >= 0 && n <= 100
            data Line = { sku: String, quantity: Qty, flag: Bool, note: Option<Qty> }
            data Order = { lines: List<Line>, previous: Set<String> }

            let quantityOf (l: Line): Int = if l.flag then l.quantity.value else 0

            data Common = { campaigns: Set<String> }
            data NewLead = { ...Common }
            data WorkingLead = { ...Common, touches: Int }
                invariant touches >= 1
            data OpenLead = NewLead | WorkingLead

            let touchesOf (lead: OpenLead): Int =
                match lead with
                    | NewLead -> 0
                    | WorkingLead { touches } -> touches

            let touchesTimesFive (lead: OpenLead): Int =
                match lead with
                    | NewLead -> 0
                    | WorkingLead { touches } -> touches * 5

            let sizeTimes (lead: OpenLead, k: Int): Int =
                match lead with
                    | NewLead { campaigns } -> Set.size(campaigns) * k
                    | WorkingLead { touches } -> touches
            """;

    private static final String JUDGED = """

            behavior %1$s : (order: Order, prices: Map<String, Price>, raw: Map<String, Int>,
                             rates: Map<String, Rate>, free: Int) -> Bool
            let %1$s (order, prices, raw, rates, free) = {
                let numbers = List.map(l -> %2$s, order.lines)
                List.length(numbers) == 0
                    || List.all(l -> Set.contains(l.sku, order.previous), order.lines)
            }
            """;

    private static final String JUDGED_LEAD = """

            behavior %1$s : (lead: OpenLead, priority: String, free: Int) -> Int
            let %1$s (lead, priority, free) =
                Int.min(100, %2$s + (if Set.contains(priority, lead.campaigns) then 25 else 0))
            """;

    private static final String PRICED =
            "Map.get(l.sku, prices) |> Option.withDefault(Price(0))";

    private static final String RAW = "Map.get(l.sku, raw) |> Option.withDefault(0)";

    private static final List<String> LINE_RELATION = List.of("order.lines[*].sku", "order.previous[*]");

    private static final List<String> LEAD_RELATION = List.of("lead.campaigns[*]", "priority");

    /** Each number, by name, and whether it leaves the relation read. */
    private static final Map<String, Case> CASES = cases();

    private record Case(String number, boolean read, String template, List<String> relation) {

        Case(String number, boolean read) {
            this(number, read, JUDGED, LINE_RELATION);
        }
    }

    private static Case ofALead(String number, boolean read) {
        return new Case(number, read, JUDGED_LEAD, LEAD_RELATION);
    }

    private static Map<String, Case> cases() {
        Map<String, Case> out = new LinkedHashMap<>();
        out.put("none", new Case("0", true));
        // Numbers of a newtype hold what its rules leave them, however a lookup or a name carries
        // them to the operation.
        out.put("aProductOfTwoNewtypes",
                new Case("(" + PRICED + ").value * l.quantity.value", true));
        out.put("thatProductThroughALet",
                new Case("{ let price = " + PRICED + "\n price.value * l.quantity.value }", true));
        out.put("thatSumThroughALet",
                new Case("{ let price = " + PRICED + "\n price.value + l.quantity.value }", true));
        // A choice holds what its arms hold together.
        out.put("anIfOverTwoRanges", new Case("(if l.flag then l.quantity.value else 10) + 1", true));
        out.put("anIfOverTwoRangesThroughALet",
                new Case("{ let q = if l.flag then l.quantity.value else 10\n q * 5 }", true));
        out.put("aCallThatAnswersAChoice", new Case("quantityOf(l) * 5", true));
        out.put("aChoiceInsideADifference",
                new Case("l.quantity.value - (if l.flag then 1 else 0)", true));
        // Where a number is no more than an Int the operation may pass what an Int holds. On a
        // free Int that is a stop on a place the relation does not read.
        out.put("aProductWithAFreeInt", new Case("l.quantity.value * free", true));
        out.put("aProductWithAFreeIntThroughALet",
                new Case("{ let q = l.quantity.value\n q * free }", true));
        out.put("anIfWithAnArmOfAFreeInt",
                new Case("(if l.flag then l.quantity.value else free) + 1", true));
        out.put("anIfWithAnArmOfAFreeIntThroughALet",
                new Case("{ let q = if l.flag then l.quantity.value else free\n q + 1 }", true));
        // Where it is a number the sku looks up, the stop is on the sku.
        out.put("anIfWithAnArmOfALookedUpInt",
                new Case("(if l.flag then l.quantity.value else " + RAW + ") + 1", false));
        out.put("thatIfOverALookedUpIntThroughALet",
                new Case("{ let q = if l.flag then l.quantity.value else " + RAW + "\n q + 1 }",
                        false));
        // A lookup at a key that is no place of the relation stops a run on what the relation
        // does not read, written out or bound by a let.
        out.put("aProductOfALookupAtAFixedKey",
                new Case("(Map.get(\"k\", raw) |> Option.withDefault(0)) * l.quantity.value", true));
        out.put("thatProductThroughALetOfALookupAtAFixedKey",
                new Case("{ let price = Map.get(\"k\", raw) |> Option.withDefault(0)\n"
                        + " price * l.quantity.value }", true));
        // A number a match over the cases of a value answers is the one of the case taken; a run
        // that stops on a number of one case stops on that case's places and not on the others the
        // value holds, as when the same number is read off the value where it is held.
        out.put("aProductOfAMatchOverTheCasesOfAValue", ofALead("touchesOf(lead) * 5", true));
        out.put("aSumOfAMatchOverTheCasesOfAValue", ofALead("touchesOf(lead) + 1", true));
        out.put("aNegationOfAMatchOverTheCasesOfAValue", ofALead("-touchesOf(lead)", true));
        // The same where the operation is in the arm and reads the name the arm binds.
        out.put("aProductInTheArmOfAMatch", ofALead("touchesTimesFive(lead)", true));
        out.put("aMatchWhoseArmStopsOnWhatTheRelationReads", ofALead("sizeTimes(lead, free)", false));
        // What an arm takes out of an option is a value of the type the option holds.
        // And in the arm of an attempt to build a value, which binds the value built.
        out.put("aProductInTheArmOfAnAttempt", new Case(
                "{ if Box { n = free } as b then b.n * 5 else 0 }", true));
        // And where the attempt is itself the operand, whose arm names what it built.
        out.put("anAttemptAsAFactor", new Case(
                "(if Box { n = free } as b then b.n else 0) * 5", true));
        out.put("anAttemptAsAFactorBesideALookup", new Case(
                "(if Box { n = free } as b then b.n else 0) * (" + RAW + ")", false));
        // A field of a record is where the rules of the record leave it, whatever made the record:
        // the field of one built from a lookup is bounded where its rules bound it, and is as open
        // as the lookup where they do not.
        out.put("aFieldOfARecordWhoseRulesBoundIt", new Case(
                "{ if Tray { n = " + RAW + " } as t then t.n * 5 else 0 }", true));
        out.put("aFieldOfARecordWhoseRulesLeaveItOpen", new Case(
                "{ if Box { n = " + RAW + " } as b then b.n * 5 else 0 }", false));
        // The range of an attempt that is itself the operand is the range of its arms: what the
        // record's rules bound the field to, and nought.
        out.put("anAttemptAsAFactorWhoseRulesBoundTheField", new Case(
                "(if Tray { n = " + RAW + " } as t then t.n else 0) * 5", true));
        out.put("anAttemptAsAFactorWhoseRulesLeaveTheFieldOpen", new Case(
                "(if Box { n = " + RAW + " } as b then b.n else 0) * 5", false));
        out.put("aMatchOverAnOptionOfANewtype", new Case(
                "{ match l.note with\n | Some n -> n.value * 5\n | None -> 0 }", true));
        // The name an arm binds is read the same whether the operation is in the arm or the match
        // is its operand.
        out.put("anOperationInTheArmOfAMatchOverAnOption", new Case(
                "{ match l.note with\n | Some n -> n.value * free\n | None -> 0 }", true));
        out.put("aMatchOverAnOptionAsAFactor", new Case(
                "(match l.note with\n | Some n -> n.value\n | None -> 0) * free", true));
        // A Decimal weighted by a rate the sku looks up, converted through the option the lookup
        // answers and rounded: the number a run works out is the rounded Decimal, whose rate is
        // positive and whose quantity is no more than the newtype leaves it.
        out.put("aRoundedDecimalOfALookedUpRate", new Case(
                "Map.get(l.sku, rates) |> Option.map(rate -> Decimal.round(2, HALF_UP,"
                        + " Decimal.fromInt(l.quantity.value) * rate.value * 0.01m))", true));
        out.put("thatRoundedDecimalThroughALet", new Case(
                "{ let weighted = Map.get(l.sku, rates) |> Option.map(rate -> Decimal.round(2,"
                        + " HALF_UP, Decimal.fromInt(l.quantity.value) * rate.value * 0.01m))\n"
                        + " weighted }", true));
        out.put("aProductOfLookedUpInts", new Case("(" + RAW + ") * l.quantity.value", false));
        out.put("aLookedUpProductThroughALet",
                new Case("{ let price = " + RAW + "\n price * l.quantity.value }", false));
        return out;
    }

    /** Every case measured, by name: one model, compiled and measured once for the class. */
    private static final Map<String, PartitionEvidence> MEASURED = measured();

    private static Map<String, PartitionEvidence> measured() {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        CASES.forEach((name, each) -> source.append(each.template().formatted(name, each.number())));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        Map<String, PartitionEvidence> out =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        assertNotNull(out, "the model under test compiles");
        return out;
    }

    private static List<String> readAs(String name, UndividedPosition.Reason reason) {
        PartitionEvidence evidence = MEASURED.get(name);
        assertNotNull(evidence, () -> name + " is measured");
        return evidence.notRead().stream().filter(each -> each.reason() == reason)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    @Test
    void aNumberOfAKnownRangeLeavesTheRelationReadAndOneThatMayPassAnIntTiesIt() {
        Map<String, List<List<String>>> differs = new LinkedHashMap<>();
        CASES.forEach((name, each) -> {
            List<List<String>> expected = each.read() ? List.of(each.relation(), List.of())
                    : List.of(List.of(), each.relation());
            List<List<String>> actual = List.of(
                    readAs(name, UndividedPosition.Reason.RULE_RELATING_TWO_VALUES),
                    readAs(name, UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE));
            if (!expected.equals(actual)) {
                differs.put(name, actual);
            }
        });
        assertEquals(Map.of(), differs);
    }

    @Test
    void aNameAnArmBindsIsReadAlikeWhereTheOperationIsInTheArmAndWhereTheMatchIsItsOperand() {
        for (UndividedPosition.Reason reason : UndividedPosition.Reason.values()) {
            assertEquals(readAs("anOperationInTheArmOfAMatchOverAnOption", reason),
                    readAs("aMatchOverAnOptionAsAFactor", reason), reason.toString());
        }
    }

    @Test
    void aNumberWrittenThroughALetIsTheNumberWrittenOut() {
        for (UndividedPosition.Reason reason : UndividedPosition.Reason.values()) {
            assertEquals(readAs("aProductOfLookedUpInts", reason),
                    readAs("aLookedUpProductThroughALet", reason), reason.toString());
        }
    }
}
