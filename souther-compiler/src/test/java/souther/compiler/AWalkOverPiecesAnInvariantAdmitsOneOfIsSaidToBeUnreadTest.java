package souther.compiler;

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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rewrite left open where a rule of a position refused candidates says the rule was not read,
 * and not that the search ran short.
 *
 * <p>The invariant admits one separator, so every string with a piece more is refused, and the
 * values it admits are not read to make others. Which strings come apart into more pieces is what
 * the invariant says, and this compiler does not derive that from a pattern.
 */
class AWalkOverPiecesAnInvariantAdmitsOneOfIsSaidToBeUnreadTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String ONE_SEPARATOR = """
            module repro.domains

            data Email = String
                invariant String.matches("[^@]+@[^@]+", value)

            behavior domains : (e: Email) -> List<String>
            let domains (e) = List.map(d -> String.lowercase(d), List.drop(1, String.split("@", e.value)))

            example domains
                | "one" : (Email("a@B")) -> [ "b" ]
            """;

    private static final String NO_INVARIANT = ONE_SEPARATOR.replace(
            "    invariant String.matches(\"[^@]+@[^@]+\", value)\n", "");

    @Test
    void aRuleThatRefusedCandidatesIsSaidNotToBeRead() {
        List<List<String>> because = openRewrites(ONE_SEPARATOR);

        assertEquals(2, because.size());
        for (List<String> each : because) {
            assertTrue(each.contains("a_rule_was_not_read"), each::toString);
            assertFalse(each.contains("runs_spent"), each::toString);
        }
    }

    @Test
    void whereNoRuleRefusedAnythingTheRewritesAreDecided() {
        assertEquals(List.of(), openRewrites(NO_INVARIANT));
    }

    /** The words each open rewrite of the first behavior is open for. */
    private static List<List<String>> openRewrites(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        JsonNode replacement = JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("replacement");
        List<List<String>> out = new ArrayList<>();
        for (JsonNode each : replacement.get("obligations")) {
            if (each.has("undecidedBecause")) {
                List<String> words = new ArrayList<>();
                each.get("undecidedBecause").forEach(word -> words.add(word.asString()));
                out.add(words);
            }
        }
        return out;
    }
}
