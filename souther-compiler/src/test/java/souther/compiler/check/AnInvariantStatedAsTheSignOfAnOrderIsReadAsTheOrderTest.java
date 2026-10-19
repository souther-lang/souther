package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * An invariant stated as {@code compare(a, b) op 0} is read as the one stated as {@code a op b}.
 *
 * <p>Held to the report of the invariant written between the two values, so a place the sign
 * leaves unread is one the order leaves unread for the same reason.
 */
class AnInvariantStatedAsTheSignOfAnOrderIsReadAsTheOrderTest {

    private static String model(String rule) {
        return """
                module m

                data Price = Decimal
                    invariant %s
                data Pair = { lo: Price, hi: Price }

                behavior pick : (l: Pair) -> Int
                let pick (l) = if l.lo.value > 3.0m then 1 else 0
                """.formatted(rule);
    }

    private static String report(String rule) {
        Compilation compilation = Compilation.ofSource(model(rule), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void theSignOfAnOrderAgainstNoughtIsTheOrder() {
        String sign = report("Decimal.compare(value, 5.0m) <= 0");
        assertFalse(sign.contains("not read: invariant Price"), sign);
        assertEquals(report("value <= 5.0m"), sign);
    }
}
