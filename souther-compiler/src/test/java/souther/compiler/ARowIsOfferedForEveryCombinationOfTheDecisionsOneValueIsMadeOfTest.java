package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;

import java.util.Map;
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
}
