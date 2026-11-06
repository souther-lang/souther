package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Where two names stand for elements of one container, a point of a line on the element read second
 * is not refuted by what the way asks of the other name.
 *
 * <p>Every value the declarations allow an element is held by some element of some list, so a row
 * reaches every point of {@code b.n >= 1} past {@code a.n < 0}. How the way to a line is kept to
 * the elements the line reads is asked of its owner
 * ({@link TheWayToALineIsKeptToTheElementsTheLineReadsTest}); this asks only that a report made of
 * the line refutes none of its points.
 */
class APointOfALineOnOneNamesElementIsNotRefutedByWhatIsAskedOfAnotherTest {

    private static final String MODEL = """
            module probe.namedpoints

            data Item = { n: Int }
                invariant n >= -10 && n <= 10
            data Input = { items: List<Item> }

            behavior joined : (x: Input) -> Int
            let joined (x) = List.sum(List.map(a -> List.sum(List.map(b ->
                if a.n < 0 && b.n >= 1 then 1 else 0, x.items)), x.items))
            """;

    @Test
    void noPointOfTheLineOnTheSecondNameIsRefuted() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        assertEquals(List.of(), made.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                "the model compiles");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        List<JsonNode> obligations = new ArrayList<>();
        collect(JsonMapper.builder().build().readTree(AdequacyReport.of(made)
                .json(SourceRendering.namedByIdentity(made.texts()))), obligations);
        assertFalse(obligations.isEmpty(), "the lines are owed points");
        assertEquals(List.of(), obligations.stream()
                .filter(each -> "refuted".equals(each.get("disposition").asString()))
                .map(each -> each.get("rule").asString() + " " + each.get("point").asString())
                .toList());
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("disposition") && node.has("knownWritable")
                && node.has("rule")) {
            out.add(node);
        }
        for (JsonNode child : node) {
            collect(child, out);
        }
    }
}
