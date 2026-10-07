package souther.compiler;

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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point of a line behind a condition, where no row reaching the line holds a value, is owed and
 * refuted: counted, and never a finding.
 *
 * <p>{@code n > 10} and then {@code n == 11}. The inner line is reachable — eleven arrives — so it
 * stands, and its points are owed as the line's points always are. Two of them lie where the way
 * leaves nothing: ten, and below ten. The position admits both, which is what the rules of the
 * position prove; no row reaching the inner comparison holds either, which is what a search over the
 * way proves. The point asks the second question, so the second answer is the point's.
 *
 * <p>The outer line is the control: nothing stands before it, a ten reaches it, and its points are
 * what they were.
 */
class APointTheWayLeavesNoValueIsRefutedTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module probe.refuted

            behavior nested : (n: Int) -> String
            let nested (n) = if n > 10 then (if n == 11 then "a" else "b") else "c"

            example nested
                | (0) -> "c"
            """;

    @Test
    void thePointsTheWayLeavesNothingAreRefuted() {
        Map<String, String> inner = dispositions("comparison@0:4:39");
        assertEquals("refuted", inner.get("off below"),
                () -> "no row reaching the inner line holds ten: " + inner);
        assertEquals("refuted", inner.get("out below"),
                () -> "nor anything below ten: " + inner);
        assertTrue(inner.entrySet().stream()
                        .filter(each -> !each.getKey().endsWith("below"))
                        .noneMatch(each -> each.getValue().equals("refuted")),
                () -> "the points the way does reach are owed rows as before: " + inner);
    }

    @Test
    void aLineNothingStandsBeforeIsAsItWas() {
        Map<String, String> outer = dispositions("comparison@0:4:23");
        assertTrue(outer.values().stream().noneMatch("refuted"::equals),
                () -> "a ten reaches the outer line: " + outer);
    }

    @Test
    void aRefutedPointIsNoFinding() {
        Compilation compilation = measured();
        String human = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(human.contains("refuted 2"), human);
        assertFalse(human.contains("! no row is at the OFF point below the line (comparison@4:39)"),
                human);
        assertFalse(human.contains("! no row is at an OUT point below the line (comparison@4:39)"),
                human);
    }

    /** Each point of the line at {@code rule}, by which point and side, with its disposition. */
    private static Map<String, String> dispositions(String rule) {
        Compilation compilation = measured();
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        Map<String, String> out = new LinkedHashMap<>();
        List<JsonNode> found = new ArrayList<>();
        collect(document, found);
        for (JsonNode each : found) {
            if (!rule.equals(each.get("rule").asString())) {
                continue;
            }
            JsonNode side = each.get("obligationId").get("location").get("side");
            out.put(each.get("point").asString() + (side == null ? "" : " " + side.asString()),
                    each.get("disposition").asString());
        }
        assertTrue(!out.isEmpty(), () -> "the line at " + rule + " is owed points: " + document);
        return out;
    }

    /** Every obligation of the document that says where its evidence puts it. */
    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("disposition") && node.has("knownWritable")
                && node.has("rule")) {
            out.add(node);
        }
        for (JsonNode child : node) {
            collect(child, out);
        }
    }

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(e -> e.diagnostic().code().toString()).toList(), "the model is measured");
        return compilation;
    }
}
