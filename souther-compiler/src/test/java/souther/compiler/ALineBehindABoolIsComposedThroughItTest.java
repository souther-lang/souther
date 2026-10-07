package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.Generator;
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
 * A line behind a condition that reads a {@code Bool} position has rows composed through that
 * condition: each point's row writes the value of the point and the truth the way asks for.
 *
 * <p>{@code a.n.value > 100} stands where {@code a.flag} came out false, so every row at one of its
 * points holds {@code flag = false}. The rules of {@code n} alone are not taken as proof that a row
 * can be written at a point behind a condition, so what shows it here is a row composed through the
 * condition — and with one, each point is one a row can be written at, and the report says whether
 * a row is there rather than leaving it undecided.
 */
class ALineBehindABoolIsComposedThroughItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * The line, behind {@code condition} coming out false — with one row past the condition the
     * other way, which writes {@code n} at the declaration's own line and leaves the rows offered to
     * be the ones at the line under test.
     */
    private static String behind(String condition, boolean past) {
        return """
            module probe.truth

            data N = Int invariant value >= 100
            data Amount = { flag: Bool, n: N }
            data Ok = { n: Int }
            data Refused = { why: String }

            behavior charge : (a: Amount) -> Ok | Refused
                constructs Ok, Refused
            let charge (a) =
                if %s then
                    Ok { n = 1 }
                else
                    if a.n.value > 100 then Ok { n = 2 } else Refused { why = "small" }

            example charge
                | (Amount { flag = %s, n = N(100) }) -> Ok { n = 1 }
            """.formatted(condition, past);
    }

    private static final String UNDER_A_CASE = """
            module probe.truth

            data N = Int invariant value >= 100
            data Plain = { note: Int }
            data Special = { flag: Bool }
            data Kind = Plain | Special
            data Amount = { kind: Kind, n: N }
            data Ok = { n: Int }
            data Refused = { why: String }

            behavior charge : (a: Amount) -> Ok | Refused
                constructs Ok, Refused
            let charge (a) =
                match a.kind with
                | Plain { note } -> Ok { n = note }
                | Special { flag } ->
                    if flag then
                        Ok { n = 1 }
                    else
                        if a.n.value > 100 then Ok { n = 2 } else Refused { why = "small" }

            example charge
                | (Amount { kind = Plain { note = 0 }, n = N(100) }) -> Ok { n = 0 }
            """;

    @Test
    void everyPointBehindTheTruthIsOneARowCanBeWrittenAt() {
        Map<String, JsonNode> points = pointsOf(measured(behind("a.flag", true)),
                "comparison@0:14:22");
        assertEquals(List.of("on", "off", "in"), List.copyOf(points.keySet()),
                () -> "the line's owed points: " + points);
        points.forEach((point, owed) -> {
            assertTrue(owed.get("knownWritable").asBoolean(),
                    () -> "a row composed through the truth shows one can be written: " + owed);
            assertEquals("unmet", owed.get("disposition").asString(),
                    () -> "no row is there, and nothing leaves that open: " + owed);
        });
    }

    @Test
    void theRowAtEachPointWritesTheTruthTheWayAsksFor() {
        assertEquals(List.of(
                        "a.n = 101: Amount { flag = false, n = N(101) }",
                        "a.n = 100: Amount { flag = false, n = N(100) }",
                        "101 < a.n: Amount { flag = false, n = N(102) }"),
                offered(measured(behind("a.flag", true))));
    }

    /** The other way round, so a row that wrote one value whatever the way asked fails one of the
     *  two. */
    @Test
    void aDeniedTruthAsksForTheOtherValue() {
        assertEquals(List.of(
                        "a.n = 101: Amount { flag = true, n = N(101) }",
                        "a.n = 100: Amount { flag = true, n = N(100) }",
                        "101 < a.n: Amount { flag = true, n = N(102) }"),
                offered(measured(behind("Bool.not(a.flag)", false))));
    }

    /** A truth read at a position under a case is written there, under the case the fork took. */
    @Test
    void aTruthUnderACaseIsWrittenUnderThatCase() {
        assertEquals(List.of(
                        "a.n = 101: Amount { kind = Special { flag = false }, n = N(101) }",
                        "a.n = 100: Amount { kind = Special { flag = false }, n = N(100) }",
                        "101 < a.n: Amount { kind = Special { flag = false }, n = N(102) }"),
                offered(measured(UNDER_A_CASE)));
    }

    /** Each row offered to {@code charge}, as the point it is at and the value it writes. */
    private static List<String> offered(Compilation compilation) {
        Generator.GenerationResult filled = OfferedAtTheLines.of(compilation,
                compilation.modules().getFirst(), "charge");
        List<String> out = new ArrayList<>();
        for (Generator.GeneratedRow row : filled.rows()) {
            out.add(String.join(", ", row.labels()) + ": " + row.inputs().getFirst().text());
        }
        return out;
    }

    /** The owed points of the line at {@code rule}, by which point. */
    private static Map<String, JsonNode> pointsOf(Compilation compilation, String rule) {
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<JsonNode> found = new ArrayList<>();
        collect(document, found);
        Map<String, JsonNode> out = new LinkedHashMap<>();
        for (JsonNode each : found) {
            if (rule.equals(each.get("rule").asString())) {
                out.put(each.get("point").asString(), each);
            }
        }
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

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(e -> e.diagnostic().code().toString()).toList(), "the model is measured");
        return compilation;
    }
}
