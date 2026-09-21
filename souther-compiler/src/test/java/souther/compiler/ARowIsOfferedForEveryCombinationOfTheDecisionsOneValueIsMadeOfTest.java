package souther.compiler;

import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAccount;
import souther.compiler.query.Compilation;
import souther.compiler.query.Composition;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.RowKey;
import souther.compiler.query.Settlement;
import souther.compiler.query.Settlements;
import souther.compiler.query.UnderABudget;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A charge that is the sum of two decisions owes a row where both of them are live.
 *
 * <p>Rows offered for the product of the input positions are offered for what the types divide,
 * which is not what the body reads. Two decisions meeting at one operator are what one answer is
 * made of, and a row that leaves either of them at the value it takes when nothing happens cannot
 * tell that operator from another one over the same two numbers.
 */
class ARowIsOfferedForEveryCombinationOfTheDecisionsOneValueIsMadeOfTest {

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

    /** The inputs of a row where the base charge is owed and the express charge is owed with it. */
    private static final Pattern BOTH_LIVE =
            Pattern.compile("Total\\((\\d+)\\),\\s*Standard,\\s*Express");

    private static String block(String source) {
        return block(Compilation.ofSource(source, "Main"));
    }

    /** The same, with the offering held to {@code rowLimit} rows and nothing else about the budget
     *  changed. */
    private static String block(String source, int rowLimit) {
        return block(UnderABudget.of(Compilation.ofSource(source, "Main"),
                new AdequacyPolicy(Budgets.measures(),
                        new AdequacyPolicy.OfTheGeneration(rowLimit,
                                Budgets.generation().cellsPerGroup()))));
    }

    private static String block(Compilation compilation) {
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return blockOf(compilation);
    }

    /** The same, for a caller whose compilation is measured and answered already. */
    private static String blockOf(Compilation compilation) {
        Map<String, Adequacy.Filling> filling = Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(filling, "the model under test compiles");
        return GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        souther.compiler.query.OfferingRequest.overTheModule(
                                compilation.modules().get(0))),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db()).text();
    }

    /** A fresh compilation, measured once, for a caller asking more than one question of it. */
    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /** The offering's own table of what each row would settle, built the way an offering is. */
    private static Settlements settlementsOf(Compilation compilation) {
        OfferingRequest request = OfferingRequest.overTheModule(compilation.modules().get(0));
        Map<String, Adequacy.Filling> generated =
                Adequacy.generatedOf(compilation.db(), request.module());
        BorderAccount account = Adequacy.accountFor(compilation.db(), request.module(),
                request.scope());
        Composition composed = Composition.composed(request, generated, account);
        return Settlements.of(compilation.db(), composed);
    }

    /** The combinations of one behavior's decisions nothing has made, as the account states them. */
    private static Set<ObligationIdentity.OfACombinationOfDecisions> meetingsOf(
            Compilation compilation) {
        Set<ObligationIdentity.OfACombinationOfDecisions> out = new LinkedHashSet<>();
        for (Adequacy.Finding each : AdequacyReport.of(compilation).adequacyGaps()) {
            if (each.about() instanceof About.ACombinationNoRowMakes(var combination)) {
                out.add(combination);
            }
        }
        return out;
    }

    @Test
    void aRowIsOfferedWhereBothChargesAreOwedAtOnce() {
        String block = block(SHIPPING);

        Matcher m = BOTH_LIVE.matcher(block);
        boolean found = false;
        while (m.find()) {
            if (Long.parseLong(m.group(1)) < 5000) {
                found = true;
            }
        }
        assertTrue(found,
                "the only answer both decisions take part in is the one where a Standard member "
                        + "under the free-shipping line pays for express, and no row offered sits "
                        + "there: " + block);
    }

    /** How many rows the offering here is held to, which is fewer than the product of the decisions
     *  below has combinations and so is the limit a group of them would reach. */
    private static final int ROWS_ALLOWED = 20;

    /** Three three-way decisions summed, whose full product is 27 combinations. */
    private static final String THREE = """
            module example.three

            data Tier = Bronze | Silver | Gold

            behavior fee : (a: Tier, b: Tier, c: Tier) -> Int

            let rate (tier: Tier): Int =
                match tier with
                    | Bronze -> 0
                    | Silver -> 1
                    | Gold -> 2

            let fee (a, b, c) = rate(a) + rate(b) + rate(c)
            """;

    /** Two decisions whose conditions the reading cannot say a position for. */
    private static final String MIXED = """
            module example.mixed

            behavior fee : (a: Int, b: Int) -> Int

            let fee (a, b) =
                (if a > 1 && b > 2 then 1 else 0) + (if a > 3 || b > 4 then 1 else 0)
            """;

    /** How many rows the block writes, named or not. */
    private static int rows(String block) {
        return (int) block.lines().filter(line -> line.startsWith("    | ")).count();
    }

    /** {@code | "name" : (inputs)} as the block writes it, over lines the formatter may have wrapped. */
    private static final Pattern OFFERED = Pattern.compile("\\|\\s*\"((?:[^\"\\\\]|\\\\.)*)\"\\s*\\n?\\s*:");

    /** The names the block offers, in the order it writes them. */
    private static List<String> names(String block) {
        List<String> found = new java.util.ArrayList<>();
        Matcher m = OFFERED.matcher(block.replace("//", ""));
        while (m.find()) {
            found.add(m.group(1));
        }
        return found;
    }

    /**
     * A group's combinations cost rows only where an arm is owed one.
     *
     * <p>A group has as many combinations as the product of its factors, which grows with the body
     * rather than with the number of inputs. Offered for their own sake they were a list nobody
     * reads, and the row limit was what stood between an author and it. Nothing is owed a row for a
     * combination now, so what a group costs is bounded by its arms — of which a body has as many
     * as it has ways through, and every one of them is a line the author wrote.
     */
    @Test
    void aGroupCostsRowsOnlyWhereAnArmIsOwedOne() {
        String block = block(THREE, ROWS_ALLOWED);

        assertTrue(rows(block) <= ROWS_ALLOWED,
                "the rows offered stay inside the row limit: " + rows(block));
        assertFalse(block.contains("generation stopped"),
                "and the search does not run out, the combinations costing nothing of their own: "
                        + block);
    }

    /**
     * A factor no row can be steered around takes its group with it. Under a condition mixing
     * {@code &&} and {@code ||} the arm cannot say which comparison came out which way, so the
     * decision places at no class — and a cell over it is the same row asked for twice, offered
     * under a name that says nothing.
     */
    @Test
    void aGroupWithAFactorNothingCanSteerIsNotOffered() {
        List<String> offered = names(block(MIXED));

        assertTrue(offered.stream().noneMatch(String::isEmpty),
                "no row is offered under an empty name: " + offered);
    }

    /** A charge one of whose arms says the case cannot arise. */
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
     * What the interaction reading will not count as an outcome is still a class the rules admit.
     *
     * <p>Two questions with two answers, and they do not have to agree. An arm answering
     * {@code unreachable} is not a way the charge on the left is settled, so it is not a factor and
     * the sum is not a group. What the types say the position holds has not changed, so a row at
     * that class is owed exactly as it was — a model's own claim about what cannot arise must not
     * take away the row that would show the claim wrong.
     */
    @Test
    void aClassTheBodyDeclaresUnreachableIsStillOwedARow() {
        String block = block(ABORTING);

        assertTrue(block.contains("(B, "),
                "the class the body says cannot arise is still one a row is offered at: " + block);
    }

    /** Two decisions of three and four outcomes, whose group has twelve combinations. */
    private static final String TWELVE = """
            module example.twelve

            data Tier = Bronze | Silver | Gold
            data Speed = Slow | Mid | Fast | Warp

            behavior fee : (tier: Tier, speed: Speed) -> Int

            let rate (t: Tier): Int =
                match t with
                    | Bronze -> 0
                    | Silver -> 1
                    | Gold -> 2

            let extra (s: Speed): Int =
                match s with
                    | Slow -> 0
                    | Mid -> 1
                    | Fast -> 2
                    | Warp -> 3

            let fee (tier, speed) = rate(tier) + extra(speed)
            """;

    /**
     * A group's combinations cost no rows of their own, and the body's own rules do.
     *
     * <p>The twelve rows here are not the group's twelve cells. A combination is where the search
     * looks and is owed nothing; what is owed is what the model states, and this body states twelve
     * rules — one per way through it, which is what three outcomes against four make when both are
     * decided on. Five of them are answered by the rows the classes are offered, and the other
     * seven are rows of their own.
     *
     * <p>So what a group costs is bounded by the ways the author wrote rather than by the space the
     * search walks, which is the same sentence the arms are held to one measure over. That the
     * difference is real is the sibling above: a group whose cells nothing is owed at costs
     * nothing, however many cells it has.
     */
    @Test
    void aGroupsCombinationsCostNoRowsOfTheirOwn() {
        String block = block(TWELVE);

        assertEquals(12, rows(block),
                "one row per rule of the decision, five of them the classes' own: " + block);
        assertTrue(!block.contains("generation stopped"),
                "and nothing was left for a limit to cut off: " + block);
    }

    /** Three decisions summed inside the arm of a fork above them. */
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

                        counted
                    }
            """;

    /**
     * And a body whose decisions sit inside an arm is offered a row for each of their combinations.
     *
     * <p>The interaction measure is made from the body's own structure and not from reading rows,
     * so the eight ways the three decisions can come out are owed a row whether or not this model
     * has an {@code example} block: nothing having read a row is nothing having made any of them,
     * which is the same news the measure gives a model with rows that miss a combination.
     *
     * <p>Checked twice over, and not only by the count the block writes. A row count that came out
     * right while the obligation it answered was never requested is exactly what an offering's own
     * reduction can no longer tell from a row genuinely owed — so this reads the requested/composed/
     * settled bookkeeping directly before it reads the count the count alone cannot distinguish
     * this from.
     */
    @Test
    void aBodyWhoseDecisionsSitInsideAnArmIsOfferedRowsForTheirUnmadeMeetings() {
        Compilation compilation = measured(INSIDE_AN_ARM);

        Set<ObligationIdentity.OfACombinationOfDecisions> meetings = meetingsOf(compilation);
        assertEquals(8, meetings.size(), () -> "the eight ways the three decisions under the B arm"
                + " can come out, none of them made without a row: " + meetings);

        Settlements table = settlementsOf(compilation);
        for (ObligationIdentity.OfACombinationOfDecisions meeting : meetings) {
            assertTrue(table.requested().contains(meeting),
                    () -> meeting + " is requested: " + table.requested());
            RowKey row = table.composedFor().get(meeting);
            assertNotNull(row, () -> "a row was composed for " + meeting);
            assertInstanceOf(Settlement.Settles.class, table.at(row, meeting),
                    () -> "and it settles what it was composed for: " + meeting);
        }

        String block = blockOf(compilation);
        assertEquals(List.of(), names(block).stream().filter(name -> name.contains(" x ")).toList(),
                "every row is named for one class, none for a combination of them: " + block);
        assertEquals(9, rows(block),
                "one row for the choice's other class and one apiece for the eight combinations"
                        + " under this one, since none of them is made without a row: " + block);
    }
}
