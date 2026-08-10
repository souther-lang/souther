package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a build refuses, the generator answers — with a row, or with why there is none.
 *
 * <p>A generator that offers rows for the gaps it has a strategy for and says nothing about the rest
 * reads as though the block filled everything. An author who takes every row it offers is left with a
 * model that still fails, and nothing told them which part of the shortfall was never attempted.
 *
 * <p>So the answer is total over the findings a build refuses. Which of the three it is depends on
 * whether a strategy applies, not on what a search happened to do: a strategy that recognised the gap
 * and composed nothing is not the same as no strategy for the gap at all.
 */
class EveryGapTheBuildRefusesGetsAnAnswerTest {

    /** Two boundary gaps a strategy composes a row for, and an arm no strategy reaches. */
    private static final String POLICY = """
            module example.policy

            data Rate = Int
                invariant nonNegative = value >= 0

            data Cap = Int
                invariant nonNegative = value >= 0

            data Policy =
                { rate: Rate
                , cap: Cap
                }

            behavior fee : (days: Int, policy: Policy) -> Int

            let fee (days, policy) = {
                let accrued = days * policy.rate.value

                if accrued > policy.cap.value then policy.cap.value else accrued
            }

            example fee
                | "under the cap" : (5, Policy { rate = Rate(10), cap = Cap(500) }) -> 50
            """;

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    private static List<Adequacy.Finding> gaps(Compilation compilation, String module,
                                               String behavior) {
        Map<String, List<Adequacy.Finding>> found =
                compilation.db().ask(new Adequacy.Findings(module)).value();
        assertNotNull(found, "the model under test compiles");
        return found.get(behavior).stream().filter(Adequacy.Finding::isAdequacyGap).toList();
    }

    private static Adequacy.Filling filling(Compilation compilation, String module,
                                            String behavior) {
        Map<String, Adequacy.Filling> generated =
                compilation.db().ask(new Adequacy.Generated(module)).value();
        assertNotNull(generated, "the model under test compiles");
        return generated.get(behavior);
    }

    @Test
    void everyGapTheBuildRefusesHasOneAnswer() {
        Compilation compilation = compiled(POLICY);
        List<Adequacy.Finding> gaps = gaps(compilation, "example.policy", "fee");

        assertFalse(gaps.isEmpty(), "the model under test has gaps to answer for");
        assertEquals(gaps,
                filling(compilation, "example.policy", "fee").gaps().stream()
                        .map(Adequacy.GapDisposition::gap).toList(),
                "one answer per gap, in the order the findings were established");
    }

    @Test
    void aBoundaryARowWasComposedForIsAnswerdWithThatRow() {
        Compilation compilation = compiled(POLICY);
        List<Adequacy.GapDisposition> answered =
                filling(compilation, "example.policy", "fee").gaps().stream()
                        .filter(d -> d.gap().kind() == Adequacy.Kind.BOUNDARY_UNMET).toList();

        assertEquals(2, answered.size(), "both edges");
        assertTrue(answered.stream().allMatch(
                        d -> d.outcome() instanceof souther.compiler.partition.GenerationOutcome.Generated),
                "a strategy applies to a boundary and it composed a row: " + answered);
    }

    @Test
    void anArmNoStrategyReachesIsNotSupportedRatherThanUnanswered() {
        Compilation compilation = compiled(POLICY);
        List<Adequacy.GapDisposition> arms =
                filling(compilation, "example.policy", "fee").gaps().stream()
                        .filter(d -> d.gap().kind() == Adequacy.Kind.ARM_UNREACHED).toList();

        assertEquals(1, arms.size());
        assertTrue(arms.get(0).outcome()
                        instanceof souther.compiler.partition.GenerationOutcome.NotSupported,
                "no strategy composes an input to reach an arm: " + arms);
    }

    @Test
    void anArmNoStrategyReachesIsNamedInTheBlock() {
        Compilation compilation = compiled(POLICY);
        Map<String, Adequacy.Filling> generated =
                compilation.db().ask(new Adequacy.Generated("example.policy")).value();
        String block = GeneratedRows.of("example.policy", generated, true);

        assertTrue(block.contains("`then`"),
                "the arm nothing offers a row for is named: " + block);
        assertTrue(block.contains("nothing offers a row"),
                "and it is told apart from an edge a strategy tried and failed at: " + block);
    }
}
