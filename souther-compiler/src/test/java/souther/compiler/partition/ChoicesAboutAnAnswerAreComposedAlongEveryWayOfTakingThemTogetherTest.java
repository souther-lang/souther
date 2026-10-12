package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSettlement;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Two choices about what a dependency answers, on places apart, are composed along every way of
 * taking them together where the figure lets them all be — and not along each alternative once
 * beside the other's first, which leaves out the one way a value meets.
 *
 * <p>The rule of the answer's type asks the two places to come to four, which only the last way of
 * taking the two choices together does: the three before it are each alternative once.
 */
class ChoicesAboutAnAnswerAreComposedAlongEveryWayOfTakingThemTogetherTest {

    private static final String ONLY_THE_LAST_WAY_COMPOSES = """
            module example.together

            data Reading = { a: Int, b: Int }
                invariant both = a + b >= 4

            data Yes
            data No
            data Answer = Yes | No

            behavior look : (at: Int) -> Reading

            behavior decides : (at: Int) -> Answer
                depends on look
            let decides (at, look) = {
                let found = look(at)
                if (found.a == 1 || found.a == 2) && (found.b == 1 || found.b == 2) then Yes
                else No
            }
            """;

    @Test
    void theWayOnlyTheLastCombinationTakesIsComposed() {
        Compilation compilation = Compilation.ofSource(ONLY_THE_LAST_WAY_COMPOSES, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        AdequacyReport report = AdequacyReport.of(compilation);
        String page = report.human(SourceRendering.namedByIdentity(compilation.texts()));
        AdequacyReport.BehaviorReport decides = report.modules().stream()
                .flatMap(module -> module.behaviors().stream())
                .filter(each -> "decides".equals(each.name()))
                .findFirst().orElseThrow();

        assertFalse(decides.ruleSettlements().isEmpty(), page);
        for (RuleSettlement each : decides.ruleSettlements().values()) {
            assertInstanceOf(RuleRequirement.Required.class, each.requirement(),
                    () -> "a row for every rule, the one past both choices included: " + each
                            + "\n" + page);
        }
    }
}
