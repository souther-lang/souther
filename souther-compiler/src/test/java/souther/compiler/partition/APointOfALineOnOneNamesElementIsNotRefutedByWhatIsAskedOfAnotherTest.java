package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Where two names stand for elements of one container, what each point of a line on the element
 * read second is owed is what it is owed where that line stands alone.
 *
 * <p>Every value the declarations allow an element is held by some element of some list, so a row
 * reaches every point of {@code b.n >= 3} past {@code a.n < -3} as it does where {@code b.n >= 3}
 * is all the body asks. What the other name asks changes where the points are reached from and not
 * what they are owed, so the two lines are compared point by point: a point refuted on one and not
 * on the other is the way kept to a name the point is not at. The two edges are apart, since
 * two edges of one quantity with no value between them owe no class between them. How the
 * way to a line is kept to the elements the line reads is asked of its owner
 * ({@link TheWayToALineIsKeptToTheElementsTheLineReadsTest}); this asks that a report made of the
 * line says the same of it.
 */
class APointOfALineOnOneNamesElementIsNotRefutedByWhatIsAskedOfAnotherTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** {@code joined}'s second comparison and {@code alone}'s only one are the same line. */
    private static final String MODEL = """
            module probe.namedpoints

            data Item = { n: Int }
                invariant n >= -10 && n <= 10
            data Input = { items: List<Item> }

            behavior joined : (x: Input) -> Int
            let joined (x) = List.sum(List.map(a -> List.sum(List.map(b ->
                if a.n < -3 && b.n >= 3 then 1 else 0, x.items)), x.items))

            behavior alone : (x: Input) -> Int
            let alone (x) = List.sum(List.map(b -> if b.n >= 3 then 1 else 0, x.items))
            """;

    @Test
    void theLineOnTheSecondNameIsOwedWhatItIsOwedAlone() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        assertEquals(List.of(), made.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                "the model compiles");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        List<JsonNode> obligations = new ArrayList<>();
        collect(JSON.readTree(AdequacyReport.of(made)
                .json(SourceRendering.namedByIdentity(made.texts()))), obligations);

        Map<String, String> joined = dispositionsOf(obligations, "joined", 2);
        Map<String, String> alone = dispositionsOf(obligations, "alone", 1);
        assertFalse(alone.isEmpty(), "the line is owed points");
        assertEquals(alone, joined);
    }

    /** Each point of the comparison numbered {@code ordinal} in {@code behavior}, by which point
     *  and side, with its disposition. */
    private static Map<String, String> dispositionsOf(List<JsonNode> obligations, String behavior,
                                                      int ordinal) {
        Map<String, String> out = new LinkedHashMap<>();
        for (JsonNode each : obligations) {
            JsonNode rule = each.get("obligationId").get("line").get("which").get("rule");
            if (rule.has("behavior") && behavior.equals(rule.get("behavior").asString())
                    && ordinal == rule.get("ordinal").asInt()) {
                JsonNode side = each.get("obligationId").get("location").get("side");
                out.put(each.get("point").asString() + (side == null ? "" : " " + side.asString()),
                        each.get("disposition").asString());
            }
        }
        return out;
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
