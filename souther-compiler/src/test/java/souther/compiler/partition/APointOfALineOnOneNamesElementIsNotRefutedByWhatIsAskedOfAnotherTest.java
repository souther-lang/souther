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
 * two edges of one quantity with no value between them owe no class between them.
 *
 * <p>Each other way of writing the names reaches the same owner and none of its points is
 * refuted; the control is one name asked twice, which leaves points no row can reach. How the way
 * to a line is kept to the elements the line reads is asked of its owner
 * ({@link TheWayToALineIsKeptToTheElementsTheLineReadsTest}); this asks that a report made of the
 * line says the same of it.
 */
class APointOfALineOnOneNamesElementIsNotRefutedByWhatIsAskedOfAnotherTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String DECLARED = """
            module probe.namedpoints

            data Item = { n: Int }
                invariant n >= -10 && n <= 10
            data Input = { items: List<Item> }

            let below (v: Item): Bool = v.n < -3
            """;

    /** Over two closures, {@code a} outside and {@code b} inside. */
    private static String inTwoClosures(String asked) {
        return "List.sum(List.map(a -> List.sum(List.map(b -> " + asked + ", x.items)), x.items))";
    }

    /** {@code joined}'s second comparison and {@code alone}'s only one are the same line. */
    private static final Map<String, String> BODIES = bodies();

    private static Map<String, String> bodies() {
        Map<String, String> out = new LinkedHashMap<>();
        out.put("joined", inTwoClosures("if a.n < -3 && b.n >= 3 then 1 else 0"));
        out.put("alone", "List.sum(List.map(b -> if b.n >= 3 then 1 else 0, x.items))");
        out.put("joinedFlipped", inTwoClosures("if b.n >= 3 && a.n < -3 then 1 else 0"));
        out.put("forkedOnAnEdge",
                inTwoClosures("if a.n < -3 then (if b.n == 3 then 1 else 2) else 3"));
        out.put("forkedOnAPoint",
                inTwoClosures("if a.n == 7 then (if b.n == 4 then 1 else 2) else 3"));
        out.put("helper", inTwoClosures("if below(a) then (if b.n >= 3 then 1 else 2) else 3"));
        out.put("denied", inTwoClosures("if Bool.not(a.n >= -3 || b.n < 3) then 1 else 2"));
        out.put("oneName", "List.sum(List.map(a ->"
                + " if a.n > 5 then (if a.n == 6 then 1 else 2) else 3, x.items))");
        return out;
    }

    /** Each obligation of the report, by the behavior of its line. */
    private static final Map<String, List<JsonNode>> OBLIGATIONS = obligations();

    private static Map<String, List<JsonNode>> obligations() {
        StringBuilder source = new StringBuilder(DECLARED);
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
        List<JsonNode> found = new ArrayList<>();
        collect(JSON.readTree(AdequacyReport.of(made)
                .json(SourceRendering.namedByIdentity(made.texts()))), found);
        Map<String, List<JsonNode>> out = new LinkedHashMap<>();
        BODIES.keySet().forEach(name -> out.put(name, new ArrayList<>()));
        for (JsonNode each : found) {
            JsonNode rule = each.get("obligationId").get("line").get("which").get("rule");
            if (rule.has("behavior")) {
                out.get(rule.get("behavior").asString()).add(each);
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

    private static List<String> refutedOf(String behavior) {
        return OBLIGATIONS.get(behavior).stream()
                .filter(each -> "refuted".equals(each.get("disposition").asString()))
                .map(each -> each.get("rule").asString() + " " + each.get("point").asString())
                .toList();
    }

    @Test
    void theLineOnTheSecondNameIsOwedWhatItIsOwedAlone() {
        Map<String, String> joined = dispositionsOf("joined", 2);
        Map<String, String> alone = dispositionsOf("alone", 1);
        assertFalse(alone.isEmpty(), "the line is owed points");
        assertEquals(alone, joined);
    }

    /** Each point of the comparison numbered {@code ordinal} in {@code behavior}, by which point
     *  and side, with its disposition. */
    private static Map<String, String> dispositionsOf(String behavior, int ordinal) {
        Map<String, String> out = new LinkedHashMap<>();
        for (JsonNode each : OBLIGATIONS.get(behavior)) {
            JsonNode rule = each.get("obligationId").get("line").get("which").get("rule");
            if (ordinal == rule.get("ordinal").asInt()) {
                JsonNode side = each.get("obligationId").get("location").get("side");
                out.put(each.get("point").asString() + (side == null ? "" : " " + side.asString()),
                        each.get("disposition").asString());
            }
        }
        return out;
    }

    /** Written another way, the second name's line is owed its points and none is refuted. */
    @Test
    void noPointIsRefutedWhicheverWayTheNamesAreWritten() {
        Map<String, List<String>> expected = new LinkedHashMap<>();
        Map<String, List<String>> actual = new LinkedHashMap<>();
        for (String shape : List.of("joinedFlipped", "forkedOnAnEdge", "forkedOnAPoint",
                "helper", "denied")) {
            assertFalse(OBLIGATIONS.get(shape).isEmpty(), shape + " is owed points");
            expected.put(shape, List.of());
            actual.put(shape, refutedOf(shape));
        }
        assertEquals(expected, actual);
    }

    /** One name held to two things leaves points no row reaches, and those are still refuted. */
    @Test
    void aPointOfOneNameHeldToTwoThingsIsStillRefuted() {
        assertFalse(refutedOf("oneName").isEmpty());
    }
}
