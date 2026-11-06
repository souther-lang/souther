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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where two names stand for elements of one container, a point of a line on the element read second
 * is refuted by nothing the way asks of the other name.
 *
 * <p>Every body here asks a bound of {@code a} and then of {@code b}, both elements of
 * {@code x.items}, and every value the declarations allow an element is held by some element of
 * some list, so a row reaches every point of every line: none is refuted, however the names are
 * written and whichever comes first. A point refuted is the way kept to the first name and the
 * point composed against it at the second.
 *
 * <p>The control is one name asked twice. {@code a.n > 5} and then {@code a.n == 6} is one element
 * held to both, and the points of the inner line that nothing satisfies are refuted.
 */
class APointOfALineOnOneNamesElementIsNotRefutedByWhatIsAskedOfAnotherTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String DECLARED = """
            data Item = { n: Int }
                invariant n >= -10 && n <= 10
            data Input = { items: List<Item> }

            let below (v: Item): Bool = v.n < 0
            """;

    private static String inTwoClosures(String asked) {
        return "List.sum(List.map(a -> List.sum(List.map(b -> " + asked + ", x.items)), x.items))";
    }

    private static final Map<String, String> TWO_NAMES = twoNames();

    private static Map<String, String> twoNames() {
        Map<String, String> out = new LinkedHashMap<>();
        out.put("joined", inTwoClosures("if a.n < 0 && b.n >= 1 then 1 else 0"));
        out.put("joinedFlipped", inTwoClosures("if b.n >= 1 && a.n < 0 then 1 else 0"));
        out.put("forkedOnAnEdge",
                inTwoClosures("if a.n < 0 then (if b.n == 1 then 1 else 2) else 3"));
        out.put("forkedOnAPoint",
                inTwoClosures("if a.n == 3 then (if b.n == 4 then 1 else 2) else 3"));
        out.put("helper",
                inTwoClosures("if below(a) then (if b.n >= 1 then 1 else 2) else 3"));
        out.put("denied", inTwoClosures("if Bool.not(a.n >= 0 || b.n < 0) then 1 else 2"));
        return out;
    }

    /** Each body by its name, and the two bodies the controls are made of. */
    private static final Map<String, String> BODIES = bodies();

    private static Map<String, String> bodies() {
        Map<String, String> out = new LinkedHashMap<>(TWO_NAMES);
        out.put("oneName", "List.sum(List.map(a ->"
                + " if a.n > 5 then (if a.n == 6 then 1 else 2) else 3, x.items))");
        return out;
    }

    /** For each body, the obligations of its comparisons that were refuted. */
    private static final Map<String, List<String>> REFUTED = refuted();

    private static Map<String, List<String>> refuted() {
        StringBuilder source = new StringBuilder("module probe.namedpoints\n\n").append(DECLARED);
        BODIES.forEach((name, body) -> source.append("""

                behavior %s : (x: Input) -> Int
                let %s (x) = %s
                """.formatted(name, name, body)));
        Compilation made = Compilation.ofSource(source.toString(), "Main");
        assertEquals(List.of(), made.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                "the model compiles");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        JsonNode document = JSON.readTree(AdequacyReport.of(made)
                .json(SourceRendering.namedByIdentity(made.texts())));
        List<JsonNode> found = new ArrayList<>();
        collect(document, found);
        Map<String, List<String>> out = new LinkedHashMap<>();
        BODIES.keySet().forEach(name -> out.put(name, new ArrayList<>()));
        for (JsonNode each : found) {
            if (!"refuted".equals(each.get("disposition").asString())) {
                continue;
            }
            String behavior = each.get("obligationId").get("line").get("which").get("rule")
                    .get("behavior").asString();
            JsonNode side = each.get("obligationId").get("location").get("side");
            out.get(behavior).add(each.get("rule").asString() + " " + each.get("point").asString()
                    + (side == null ? "" : " " + side.asString()));
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

    /** Whichever way the names are written, a row reaches every point: none is refuted. */
    @Test
    void noPointIsRefutedWhereTwoNamesAreTwoElements() {
        Map<String, List<String>> expected = new LinkedHashMap<>();
        TWO_NAMES.keySet().forEach(name -> expected.put(name, List.of()));
        Map<String, List<String>> actual = new LinkedHashMap<>();
        TWO_NAMES.keySet().forEach(name -> actual.put(name, REFUTED.get(name)));
        assertEquals(expected, actual);
    }

    /** One name held to two things leaves a point nothing satisfies, and that is still said. */
    @Test
    void aPointOfOneNameHeldToTwoThingsIsStillRefuted() {
        assertTrue(!REFUTED.get("oneName").isEmpty(),
                () -> "a point a single element cannot be at is refuted: " + REFUTED);
    }
}
