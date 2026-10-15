package souther.compiler.reading;

import org.junit.jupiter.api.Test;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.Severity;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A way into an arm that needs two positions to stand to each other the way a rule relating them
 * never leaves them is not a way in, and one the rule leaves room for is.
 *
 * <p>Two dates draw no line against each other, so whether their comparison comes out a way is
 * read off where the rules leave the two — apart, and held against each other. A day is counted,
 * so a rule that one comes before the other leaves them never level: the exclusive end is read as
 * far as it is written, and no further.
 */
class AWayThroughTwoPositionsIsOneTheRulesRelatingThemLeaveTest {

    private static String model(String rule, String asked) {
        return """
                module example.periods

                data Period = { from: Date, to: Date, n: Int }
                    invariant ordered = from RULE to
                data Yes
                data No
                data Answer = Yes | No

                behavior f : (p: Period) -> Answer
                let f (p) = if p.from ASKED p.to || p.n == 3 then Yes else No
                """.replace("RULE", rule).replace("ASKED", asked);
    }

    @Test
    void aComparisonTheRuleNeverLeavesTrueIsNoWayIn() {
        assertEquals(List.of(List.of(false, true), List.of(false, false)),
                waysThrough(model("<=", ">")), "from after to is no way in, a three is");
        assertEquals(List.of(List.of(false, true), List.of(false, false)),
                waysThrough(model("<", "==")), "two days one before the other are never level");
        assertEquals(List.of(List.of(true)),
                waysThrough(model("<", "<")), "nor the later first, so only the way it holds");
    }

    @Test
    void aComparisonTheRuleLeavesRoomForIsAWayIn() {
        assertEquals(List.of(List.of(true), List.of(false, true), List.of(false, false)),
                waysThrough(model("<=", "==")), "a day and itself are in order");
        assertEquals(List.of(List.of(true), List.of(false, true), List.of(false, false)),
                waysThrough(model("<=", "<")), "and a day before another, or level with it");
    }

    /** What each way into either arm reads of the two comparisons, in the order they are met. */
    private static List<List<Boolean>> waysThrough(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream)
                        .filter(said -> said.diagnostic().severity() == Severity.ERROR)
                        .map(said -> said.diagnostic().code() + " " + said.diagnostic().titleKey())
                        .toList(),
                "a model that did not compile answers every question with nothing");
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        CoverageRead.Read read = CoverageRead.of("f", checked.run("f"), inputs.reading(rules));
        List<List<Boolean>> out = new ArrayList<>();
        for (PathAccess access : read.arms().values()) {
            if (access instanceof PathAccess.Ways ways) {
                for (WayIn way : ways.ways()) {
                    List<Boolean> held = new ArrayList<>();
                    for (Decision each : way.decisions()) {
                        if (each.constrains() instanceof Condition.Side side) {
                            held.add(side.held());
                        }
                    }
                    out.add(held);
                }
            }
        }
        return out;
    }
}
