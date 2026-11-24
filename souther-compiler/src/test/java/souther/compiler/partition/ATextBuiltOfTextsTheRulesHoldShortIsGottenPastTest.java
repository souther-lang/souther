package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.values.TextExtents;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run to an equality over {@code v} builds a text of {@code v} on the way, which stops a run only
 * where that text, or one built on the way to it, is longer than a {@code String} holds. That is
 * where the representation stops, which parts no values: the run is taken to get past the building
 * whatever the rules hold {@code v} and the texts beside it to, the equality is read at every value
 * of {@code v}, and the building is said once as a stop of its own.
 */
class ATextBuiltOfTextsTheRulesHoldShortIsGottenPastTest {

    private static final String NOT_SHOWN_REACHED = "relation_not_shown_reached_at_every_value";

    private static final String READ = "rule_relating_two_values";

    private static final long L = TextExtents.LONGEST_STRING;

    private static String model(String rule, String text) {
        return """
                module held

                data V = String%s

                behavior f : (v: V, ns: List<String>, up: Bool) -> Bool
                let f (V(v), ns, up) = {
                    let m = %s
                    List.any(own -> own == v, ns) || String.length(m) > 0
                }
                """.formatted(rule, text);
    }

    private static String atMost(long codePoints) {
        return " invariant String.length(value) <= " + codePoints;
    }

    /** The report of {@code source}, as a person's program reads it. */
    private static JsonNode report(String source) {
        Compilation model = ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        return new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    /** Why {@code v} is not read, each reason once in the order the report gives them. */
    private static List<String> whyVIsNotRead(JsonNode report) {
        List<String> out = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition").path("notRead")) {
                    String reason = each.path("reason").asString();
                    if (each.path("position").asString().equals("v") && !out.contains(reason)) {
                        out.add(reason);
                    }
                }
            }
        }
        return out;
    }

    /** The operations the report says a run stops at only past what the representation holds. */
    private static List<String> stopsPastTheRepresentation(JsonNode report) {
        List<String> out = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition")
                        .path("stopsPastTheRepresentation")) {
                    out.add(each.path("operation").asString());
                }
            }
        }
        return out;
    }

    private static void reachedAtEveryValue(String source) {
        List<String> why = whyVIsNotRead(report(source));
        assertTrue(why.contains(READ) && !why.contains(NOT_SHOWN_REACHED),
                () -> source + " " + why);
    }

    /**
     * Two texts joined, copies, joins of a list, texts built of built texts, reversals,
     * replacements and padding: each is read at every value of {@code v}, however long the rules
     * let {@code v} be, as long as a {@code String} holds or with no rule at all.
     */
    @Test
    void aTextBuiltOfVIsGottenPastWhateverTheRulesHoldVTo() {
        for (String text : List.of("v ++ v", "String.append(v, \"ab\")", "v ++ \"ab\"",
                "String.repeat(3, v)", "String.concat([v, v, v])", "String.join(\",\", [v, v])",
                "String.concat(ns) ++ v", "(v ++ v) ++ v", "v ++ (if up then v else \"x\")",
                "String.lowercase(v) ++ \"x\"", "String.reverse(v)",
                "String.replace(\"a\", \"bb\", v)", "String.padLeft(10, \"0\", v)",
                "String.padRight(" + (L / 68 + 1) + ", \"0\", v)")) {
            for (String rule : List.of("", atMost(10), atMost(L))) {
                reachedAtEveryValue(model(rule, text));
            }
        }
    }

    /**
     * A join of a list of the input is gotten past whether the list's texts are held to a length
     * or only how many it holds is, and a list held to a few texts of any length is read as one
     * whose texts are held to ten.
     */
    @Test
    void aJoinOfAListIsGottenPastWhateverTheListsTextsAreHeldTo() {
        String joined = """
                module held

                data V = String invariant String.length(value) <= %s
                data Ws = List<String> invariant %s

                behavior f : (v: V, ns: List<String>, ws: Ws) -> Bool
                let f (V(v), ns, Ws(ws)) = {
                    let m = String.join(",", ws) ++ v
                    List.any(own -> own == v, ns) || String.length(m) > 0
                }
                """;
        for (String rule : List.of("List.length(value) <= 3",
                "List.length(value) <= 3 && List.all(s -> String.length(s) <= 10, value)")) {
            for (long longest : List.of(10L, L)) {
                reachedAtEveryValue(joined.formatted(longest, rule));
            }
        }
    }

    /** The building is said once, of the operation that builds the text. */
    @Test
    void theOperationBuildingTheTextIsSaidAsAStop() {
        assertEquals(List.of("++"), stopsPastTheRepresentation(report(model("", "v ++ v"))));
        assertEquals(List.of("String.reverse"),
                stopsPastTheRepresentation(report(model("", "String.reverse(v)"))));
    }
}
