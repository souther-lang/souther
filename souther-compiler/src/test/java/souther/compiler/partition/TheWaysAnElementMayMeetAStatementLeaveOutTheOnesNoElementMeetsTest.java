package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What some or every element is asked, taken apart into the ways an element may meet it, leaves
 * out the ways no element meets, and stops where the ones left are more than are read.
 *
 * <p>A conjunction of choices over one number is, taken apart, as many ways as the choices
 * multiplied, and nearly all of them ask an element to be at most one number and at least a larger
 * one. Those are proved closed by what the declarations leave and not looked at again, so what is
 * left is few. Where the choices are over things that do not exclude each other every way is open,
 * and past the figure the statement is said to be where this compiler's work stopped — not unread,
 * and not something a row has no words for.
 */
class TheWaysAnElementMayMeetAStatementLeaveOutTheOnesNoElementMeetsTest {

    private static final String THE_INPUT = """
            module q

            data Yes
            data No
            data Answer = Yes | No

            behavior f : (on: Int, xs: List<Int>) -> Answer
            let f (on, xs) = if BODY then Yes else No
            """;

    @Test
    void choicesNoElementMeetsTogetherAreLeftOutAndTheRestComposed() {
        List<String> parts = new ArrayList<>();
        for (int each = 0; each < 20; each++) {
            parts.add("(x <= " + each + " || x >= " + (100 + each) + ")");
        }
        Compilation compilation = compiled(
                "List.any(x -> " + String.join(" && ", parts) + ", xs)");
        String module = compilation.modules().getFirst();

        assertEquals(List.of(true, true), compilation.db()
                        .ask(new Adequacy.DecisionSearch(module, "f")).value().values().stream()
                        .map(each -> each.requirement() instanceof RuleRequirement.Required)
                        .toList(),
                "a row for each rule");
    }

    @Test
    void choicesAnElementMeetsInEveryWayStopAtTheFigureAndSaySo() {
        List<String> parts = new ArrayList<>();
        for (int each = 0; each < 10; each++) {
            parts.add("(x <= " + (100 + each) + " || x >= " + each + ")");
        }
        Compilation compilation = compiled(
                "List.any(x -> " + String.join(" && ", parts) + ", xs)");
        String human = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertTrue(human.contains("more ways an element may meet it than this compiler takes one"
                        + " by one"),
                () -> "the statement is said to be where a figure of this compiler's work stopped:\n"
                        + human);
    }

    private static Compilation compiled(String body) {
        Compilation compilation = Compilation.ofSource(THE_INPUT.replace("BODY", body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
