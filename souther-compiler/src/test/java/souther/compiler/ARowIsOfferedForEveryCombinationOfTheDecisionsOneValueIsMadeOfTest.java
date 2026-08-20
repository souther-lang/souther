package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;

import java.util.Map;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> filling = compilation.db()
                .ask(new Adequacy.Generated(compilation.modules().get(0))).value();
        assertNotNull(filling, "the model under test compiles");
        return GeneratedRows.of(compilation.modules().get(0), filling, Map.of(), false,
                SourceNameResolver.identity());
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

    /** Five three-way decisions summed, whose full product is 243 combinations. */
    private static final String FIVE = """
            module example.five

            data Tier = Bronze | Silver | Gold

            behavior fee : (a: Tier, b: Tier, c: Tier, d: Tier, e: Tier) -> Int

            let rate (tier: Tier): Int =
                match tier with
                    | Bronze -> 0
                    | Silver -> 1
                    | Gold -> 2

            let fee (a, b, c, d, e) = rate(a) + rate(b) + rate(c) + rate(d) + rate(e)
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
        return (int) block.lines().filter(line -> line.startsWith("//     | ")).count();
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
     * The cells share the budget the pairs are held to. A group has as many combinations as the
     * product of its factors, which grows with the body rather than with the number of inputs, and
     * a generation that offered all of them would hand an author a list nobody reads.
     */
    @Test
    void agroupBiggerThanTheBudgetIsOfferedWhatTheBudgetHolds() {
        String block = block(FIVE);

        assertTrue(rows(block) <= 200, "the rows offered stay inside the row limit: " + rows(block));
        assertTrue(block.contains("generation stopped"),
                "and a search that stopped says so rather than reading as complete: " + block);
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
}
