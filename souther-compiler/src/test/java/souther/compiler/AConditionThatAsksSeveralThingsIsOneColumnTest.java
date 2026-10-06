package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition that asks a row for several things is one column of the decision it is part of.
 *
 * <p>Every element of a list meeting two bounds is two relations a row is composed against, and
 * one distinction the body draws. Taken a relation at a time, the rule through it consulted the
 * one condition twice and was said with the same condition on two lines.
 */
class AConditionThatAsksSeveralThingsIsOneColumnTest {

    private static final String MODEL = """
            module probe.onecolumn

            data Line = { price: Int }
                invariant price >= 1 && price <= 100

            data Order = { lines: List<Line> }

            data Usual
            data Unusual

            behavior sort : (order: Order) -> Usual | Unusual
            let sort (order) =
                if List.all(l -> l.price >= 2 && l.price <= 90, order.lines) then Usual
                else Unusual

            example sort
                | "usual" : (Order { lines = [ Line { price = 5 } ] }) -> Usual
            """;

    @Test
    void aRuleSaysEachConditionItTurnsOnOnce() {
        String report = human();
        List<List<String>> rules = rulesSaid(report);
        assertTrue(!rules.isEmpty(), () -> "a rule no row takes is said:\n" + report);
        for (List<String> rule : rules) {
            assertEquals(rule.stream().distinct().toList(), rule,
                    () -> "a rule says each condition it turns on once:\n" + report);
        }
    }

    /** The lines under each rule no row takes, one list per rule. */
    private static List<List<String>> rulesSaid(String report) {
        List<List<String>> out = new ArrayList<>();
        List<String> rule = null;
        for (String line : report.lines().toList()) {
            if (line.contains("no row takes a decision rule")) {
                rule = new ArrayList<>();
                out.add(rule);
            } else if (rule != null && line.trim().startsWith("·")) {
                rule.add(line.trim());
            } else {
                rule = null;
            }
        }
        return out;
    }

    private static String human() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
