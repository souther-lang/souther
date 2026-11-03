package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position is read as reached at every value only over values some run gets to it at. The
 * statements on the way are kept as the form they state, and the arithmetic that wrote one can stop
 * at a partial sum that form does not show.
 */
class ARunThatStopsOnTheWayToAPositionIsNoWitnessThereTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String READ = "rule_relating_two_values";

    private static final String PARAMETERS = "a: Int, d: Int, hs: Set<Int>";

    private static final String MEMBERSHIP = "Bool.not(Set.contains(a, hs))";

    @Test
    void anInequalityWhoseFirstSumStopsDoesNotReachTheElementsAtEveryValue() {
        assertTrue(!reasonsAt("a + 9223372036854775797 - d >= 0 && " + MEMBERSHIP).contains(READ),
                () -> "" + reasonsAt("a + 9223372036854775797 - d >= 0 && " + MEMBERSHIP));
    }

    @Test
    void aRemainderWhoseFirstSumStopsDoesNotReachTheElementsAtEveryValue() {
        String condition = "Int.floorMod(9223372036854775797 + a - d, 7) >= 1 && " + MEMBERSHIP;
        assertTrue(!reasonsAt(condition).contains(READ), () -> "" + reasonsAt(condition));
    }

    @Test
    void aSumThatCancelsToTheFormStillStopsWhereItsPartialSumDoes() {
        String condition = "Int.floorMod(a + 9223372036854775807 - 9223372036854775807 - d, 7)"
                + " >= 1 && " + MEMBERSHIP;
        assertTrue(!reasonsAt(condition).contains(READ), () -> "" + reasonsAt(condition));
    }

    /**
     * The sum is worked out only on the runs where {@code d} is above nought, and the membership is
     * reached on the others without it, so no sum stops a run there.
     */
    @Test
    void aSumWorkedOutInAnArmTheMembershipIsReachedWithoutIsNoStop() {
        String condition = "(d > 0 && a + 9223372036854775797 - d >= 0) || " + MEMBERSHIP;
        assertEquals(List.of(READ), reasonsAt(condition));
    }

    /** The same sum as the left arm of a choice, worked out on every run before the membership. */
    @Test
    void aSumTheLeftArmOfAChoiceWorksOutOnEveryRunIsAStopThere() {
        String condition = "(a + 9223372036854775797 - d >= 0 || d > 0) && " + MEMBERSHIP;
        assertTrue(!reasonsAt(condition).contains(READ), () -> "" + reasonsAt(condition));
    }

    /** A form worked out wherever the rest stand keeps being read. */
    @Test
    void aFormThatIsWorkedOutEverywhereIsStillRead() {
        assertEquals(List.of(READ), reasonsAt(
                "Int.floorMod(a - d, 7) >= 1 && Bool.not(Set.contains(d, hs))"));
    }

    private static List<String> reasonsAt(String condition) {
        List<String> out = new ArrayList<>();
        JsonNode report = reportOf(compiled(condition));
        reasons(report, "hs[*]", out);
        return out.stream().distinct().toList();
    }

    private static void reasons(JsonNode node, String position, List<String> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason")
                && position.equals(node.path("position").asString())) {
            out.add(node.path("reason").asString());
        }
        node.forEach(child -> reasons(child, position, out));
    }

    private static JsonNode reportOf(Compilation compilation) {
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    private static Compilation compiled(String condition) {
        String model = """
                module demo

                behavior f : (%s) -> Bool
                let f (a, d, hs) = %s
                """.formatted(PARAMETERS, condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors());
        return compilation;
    }
}
