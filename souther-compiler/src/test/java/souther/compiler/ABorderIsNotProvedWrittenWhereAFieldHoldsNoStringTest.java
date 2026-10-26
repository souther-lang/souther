package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code String} holds only text in Normalization Form C, so a pattern whose every string is
 * changed by the form leaves no value, and nothing is proved writable beside a field of it.
 */
class ABorderIsNotProvedWrittenWhereAFieldHoldsNoStringTest {

    private static final String NEVER = """
            module example.never

            data Never = String
                invariant String.matches("a\\\\x{301}.*", value)

            data Holder = { label: Never, n: Int }

            behavior f : (h: Holder) -> Int

            let f (h) =
                if h.n >= 10 then 1 else 0
            """;

    /** The same shape over a pattern whose strings are values, which the proof is kept for. */
    private static final String WRITTEN = """
            module example.written

            data Word = String
                invariant String.matches("[a-z]+", value)

            data Holder = { label: Word, n: Int }

            behavior f : (h: Holder) -> Int

            let f (h) =
                if h.n >= 10 then 1 else 0
            """;

    @Test
    void noBorderOfAFieldBesideAStringNoValueIsIsProved() {
        List<BorderAssessment.Point> points = pointsAt(NEVER, "example.never", "f");
        assertTrue(points.stream().anyMatch(p -> p.owed() != null),
                "the body still draws its line on h.n, so there are borders to be unproved");
        assertFalse(provedAny(points), "Holder has no value, so nothing in f is proved writable");
    }

    @Test
    void theProofStandsWhereTheStringsAreValues() {
        List<BorderAssessment.Point> points = pointsAt(WRITTEN, "example.written", "f");
        assertTrue(provedAny(points), "the control: a field of values keeps the proof");
    }

    private static boolean provedAny(List<BorderAssessment.Point> points) {
        return points.stream().filter(p -> p.owed() != null)
                .anyMatch(p -> p.owed().writabilityEvidence()
                        .has(ItemAssessment.WritabilityEvidence.Ground.IT_IS_PROVED));
    }

    private static List<BorderAssessment.Point> pointsAt(String model, String module,
                                                         String behavior) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.searchedBoundariesOf(compilation.db(), module);
        assertNotNull(boundaries, "the model under test compiles");
        return BorderAssessment.pointsOf(boundaries.get(behavior));
    }
}
