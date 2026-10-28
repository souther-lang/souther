package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.partition.Replacement;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body answering one value is told from a fold over a list whose element another behavior
 * answers, by a row that holds one element.
 */
class ABodyAnsweringOneValueIsToldApartByAThrowOfAnotherBehaviorTest {

    private static final String MODEL = """
            module repro.open

            data Pin = Int
                invariant value >= 1 && value <= 12

            data Throw = List<Pin>
                invariant List.allDistinctBy(p -> p, value)

            behavior points : (t: Throw) -> Int

            let points (t) = {
                let n = List.length(t.value)
                if n == 1 then List.sum(List.map(p -> p.value, t.value)) else n
            }

            example points
                | (Throw([])) -> 0
                | (Throw([Pin(12)])) -> 12
                | (Throw([Pin(1), Pin(2)])) -> 2
                | (Throw([Pin(1), Pin(2), Pin(3)])) -> 3

            behavior score : (throws: List<Throw>) -> Int

            let score (throws) = %s

            example score
                | ([]) -> 0
            """;

    @Test
    void aWrongBodyIsToldFromAConstantByARowOfThrows() {
        assertToldApart("List.length(throws) * 100");
    }

    @Test
    void theRightBodyIsToldFromAConstantByARowOfThrows() {
        assertToldApart("List.fold((acc, t) -> acc + points(t), 0, throws)");
    }

    /** A body that answers the constant whatever it is given is the rewrite under another
     *  spelling: no row of throws answers otherwise, and nothing is owed for it. */
    @Test
    void aBodyThatAnswersTheConstantIsNoGap() {
        List<ReplacementEvidence.Outcome> oneAnswer =
                oneAnswers(rewritesOf(MODEL.formatted("0 * List.length(throws)"), "score"));

        assertTrue(oneAnswer.stream().noneMatch(ReplacementEvidence.Unnoticed.class::isInstance),
                () -> "no row of throws tells it from the constant: " + oneAnswer);
    }

    private static void assertToldApart(String body) {
        List<ReplacementEvidence.Outcome> oneAnswer =
                oneAnswers(rewritesOf(MODEL.formatted(body), "score"));

        assertEquals(1, oneAnswer.size(), () -> "a rewrite for the one value: " + oneAnswer);
        ReplacementEvidence.Unnoticed gap = assertInstanceOf(ReplacementEvidence.Unnoticed.class,
                oneAnswer.getFirst(),
                () -> "a row of throws answers otherwise than the constant: " + oneAnswer);
        ReplacementEvidence.ShownBy.AComposedRow shown = assertInstanceOf(
                ReplacementEvidence.ShownBy.AComposedRow.class, gap.shownBy(),
                "no written row shows it, so the row that does was composed");
        assertNotEquals("[]", shown.inputs().getFirst(),
                "and it holds a throw: " + shown.inputs());
    }

    private static List<ReplacementEvidence.Outcome> oneAnswers(
            Map<Replacement, ReplacementEvidence.Outcome> rewrites) {
        List<ReplacementEvidence.Outcome> out = new ArrayList<>();
        rewrites.forEach((rewrite, outcome) -> {
            if (rewrite instanceof Replacement.ByOneAnswer) {
                out.add(outcome);
            }
        });
        return out;
    }

    private static Map<Replacement, ReplacementEvidence.Outcome> rewritesOf(String source,
                                                                            String behavior) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        String module = compilation.modules().get(0);
        ReplacementEvidence its =
                compilation.db().ask(new Replacements.Measured(module)).value().get(behavior);
        Map<Replacement, ReplacementEvidence.Outcome> out = new LinkedHashMap<>();
        its.measured().made().orElseThrow(() -> new AssertionError(
                        "the rewrites were measured: " + its.measured()))
                .rewrites().forEach(each -> out.put(each.replacement(), each.outcome()));
        return out;
    }
}
