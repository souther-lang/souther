package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.Located;
import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A warning about a rule no row takes marks each call of a helper the rule's conditions are in,
 * with which way the rule takes the condition in that call — and a warning about a point of the
 * helper's line marks the call each reading of the line was made in.
 *
 * <p>The helper's comparison is one place in the source, and the rule consults it once per call.
 * Marked only there, the conditions of the two calls are two markers on one place that a reader
 * cannot tell apart — and two rules differing only in which call went which way are two warnings
 * that read alike.
 */
class ARuleThroughAHelperCalledTwiceIsMarkedAtEachCallTest {

    private static final String MODEL = """
            module example.twice

            data Score = Int

            behavior both : (a: Int, b: Int) -> Score
                constructs Score

            let pos (n: Int): Int = if n > 0 then 1 else 0

            let both (a, b) = Score(pos(a) + pos(b))

            example both
                | "neither" : (0, 0) -> Score(0)
            """;

    @Test
    void eachCallOfTheHelperIsMarkedWithTheWayTheRuleTakesItThere() {
        List<Diagnostic> rules = warningsAboutRules();
        assertFalse(rules.isEmpty(), "the rules no row takes are warned about");

        Set<List<String>> told = new HashSet<>();
        for (Diagnostic each : rules) {
            List<LabeledRegion> calls = each.secondary().stream()
                    .filter(label -> label.said()
                            instanceof ExampleMessage.TheRuleTakesItHoldingInThisCall
                            || label.said()
                            instanceof ExampleMessage.TheRuleTakesItFailingInThisCall)
                    .toList();
            assertEquals(2, calls.size(),
                    () -> "one marker for each call of the helper: " + each.secondary());
            Set<DiagnosticPlace> places = new HashSet<>();
            calls.forEach(label -> places.add(label.place()));
            assertEquals(2, places.size(), "at the two calls, which are two places");
            assertTrue(calls.stream().allMatch(label -> called(label).equals("pos")),
                    () -> "naming what was called: " + calls);
            List<String> ways = new ArrayList<>();
            calls.forEach(label -> ways.add(label.place() + " "
                    + (label.said() instanceof ExampleMessage.TheRuleTakesItHoldingInThisCall)));
            told.add(ways);
        }
        assertEquals(rules.size(), told.size(),
                "no two rules are marked alike at the calls");
    }

    @Test
    void eachReadingOfTheHelpersLineIsMarkedAtTheCallItWasReadIn() {
        Compilation compilation = compiled();
        int warned = 0;
        for (Located each : compilation.warnings()) {
            List<ExampleMessage.TheLineIsReadInThisCall> calls = new ArrayList<>();
            Set<DiagnosticPlace> places = new HashSet<>();
            for (LabeledRegion label : each.diagnostic().secondary()) {
                if (label.said() instanceof ExampleMessage.TheLineIsReadInThisCall call) {
                    calls.add(call);
                    places.add(label.place());
                }
            }
            if (calls.isEmpty()) {
                continue;
            }
            warned++;
            assertEquals(Set.of("both/a", "both/b"),
                    Set.copyOf(calls.stream().map(ExampleMessage.TheLineIsReadInThisCall::read)
                            .toList()),
                    () -> "a marker for each reading of the line: " + calls);
            assertEquals(2, places.size(), "at the two calls, which are two places");
            assertTrue(calls.stream().allMatch(call -> call.called().equals("pos")),
                    () -> "naming what was called: " + calls);
        }
        assertTrue(warned > 0, "the points of the helper's line are warned about");
    }

    /**
     * A helper whose copy holds two conditions.
     *
     * <p>A call is one place and is marked once, whatever number of the rule's conditions its copy
     * holds: with what they all say where they say one thing, and with the rule going through the
     * call where they go different ways — which a mark at the call cannot tell apart.
     */
    private static final String TWO_CONDITIONS_A_CALL = """
            module example.inside

            data Score = Int

            behavior both : (a: Int, b: Int) -> Score
                constructs Score

            let mid (n: Int): Int = if n > 0 && n < 10 then 1 else 0

            let both (a, b) = Score(mid(a) + mid(b))

            example both
                | "neither" : (0, 0) -> Score(0)
            """;

    @Test
    void aCallIsMarkedOnce() {
        Compilation compilation = Compilation.ofSource(TWO_CONDITIONS_A_CALL, "Main");
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        int calls = 0;
        boolean wentDifferentWays = false;
        for (Located each : compilation.warnings()) {
            List<LabeledRegion> labels = each.diagnostic().secondary().stream()
                    .filter(label -> label.said()
                            instanceof ExampleMessage.TheRuleTakesItHoldingInThisCall
                            || label.said()
                            instanceof ExampleMessage.TheRuleTakesItFailingInThisCall
                            || label.said()
                            instanceof ExampleMessage.TheRuleGoesThroughItsArmInThisCall
                            || label.said()
                            instanceof ExampleMessage.TheRuleGoesThroughThisCall)
                    .toList();
            calls += labels.size();
            Set<DiagnosticPlace> places = new HashSet<>();
            labels.forEach(label -> places.add(label.place()));
            assertEquals(labels.size(), places.size(),
                    () -> "each call is marked once: " + labels);
            wentDifferentWays |= labels.stream().anyMatch(label -> label.said()
                    instanceof ExampleMessage.TheRuleGoesThroughThisCall);
        }
        assertTrue(calls > 0, "the rules through the helper's two conditions are warned about");
        assertTrue(wentDifferentWays, "and some rule takes the two conditions of one call"
                + " different ways, which is what one mark per call has to settle");
    }

    private static String called(LabeledRegion label) {
        return switch (label.said()) {
            case ExampleMessage.TheRuleTakesItHoldingInThisCall(var called) -> called;
            case ExampleMessage.TheRuleTakesItFailingInThisCall(var called) -> called;
            default -> throw new AssertionError("not a marker at a call: " + label);
        };
    }

    /** The warnings about rules of the decision no row takes. */
    private static List<Diagnostic> warningsAboutRules() {
        List<Diagnostic> out = new ArrayList<>();
        for (Located each : compiled().warnings()) {
            if (each.diagnostic().secondary().stream().anyMatch(label -> label.said()
                    instanceof ExampleMessage.TheRuleTakesThisConditionHolding
                    || label.said() instanceof ExampleMessage.TheRuleTakesThisConditionFailing)) {
                out.add(each.diagnostic());
            }
        }
        return out;
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
