package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An invariant stated as {@code compare(a, b) op 0} is read as the one stated as {@code a op b}.
 *
 * <p>Each rule is held to the report of the same rule written between the two values. The cases
 * are the ways a leaf is read that differ from one another: a bound on one value, a bound on a
 * number made from it, a bound beside another alternative, and a relation between two positions.
 */
class AnInvariantStatedAsTheSignOfAnOrderIsReadAsTheOrderTest {

    private record Same(String fields, String asSign, String asOrder, String use) {}

    private static final List<Same> RULES = List.of(
            new Same("Decimal", "Decimal.compare(value, 5.0m) <= 0", "value <= 5.0m",
                    "l.value > 3.0m"),
            new Same("Date", "Int.compare(Date.year(value), 2020) <= 0",
                    "Date.year(value) <= 2020", "Date.year(l.value) > 2000"),
            new Same("Decimal", "Decimal.compare(value, 5.0m) <= 0 || value >= 10.0m",
                    "value <= 5.0m || value >= 10.0m", "l.value > 3.0m"),
            new Same("{ a: Decimal, b: Decimal }", "0 < Decimal.compare(a, b)", "a > b",
                    "l.a > 3.0m"));

    private static String report(String fields, String rule, String use) {
        Compilation compilation = Compilation.ofSource("""
                module m

                data T = %s
                    invariant %s

                behavior pick : (l: T) -> Int
                let pick (l) = if %s then 1 else 0
                """.formatted(fields, rule, use), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void theSignOfAnOrderAgainstNoughtIsTheOrder() {
        for (Same each : RULES) {
            assertEquals(report(each.fields(), each.asOrder(), each.use()),
                    report(each.fields(), each.asSign(), each.use()),
                    () -> each.asSign() + " is read as " + each.asOrder());
        }
    }
}
