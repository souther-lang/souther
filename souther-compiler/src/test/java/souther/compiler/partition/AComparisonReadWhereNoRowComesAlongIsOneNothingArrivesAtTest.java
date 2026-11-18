package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comparison of two positions read only along a way no row comes along is one nothing arrives
 * at. Every address holds an {@code @}, so the arm a split finding none takes is taken by no row:
 * what the comparison reads there is no statement about any row, and that every value of the two
 * gets to it is not said either.
 */
class AComparisonReadWhereNoRowComesAlongIsOneNothingArrivesAtTest {

    private static final String NOTHING_ARRIVES = "nothing_arrives_at_the_rules_line";

    private static final String RESTRICTED = "position_restricted_to_what_a_rule_admits";

    private static final String COMPARED = "if other == email then 2 else 3";

    @Test
    void comparedOnlyWhereNoAddressLacksTheSeparatorNothingArrives() {
        assertEquals(Map.of("email", List.of(NOTHING_ARRIVES, RESTRICTED),
                        "other", List.of(NOTHING_ARRIVES, RESTRICTED)),
                readingsOf("1", COMPARED));
    }

    @Test
    void comparedWhereEveryAddressGoesTheComparisonIsReached() {
        Map<String, List<String>> read = readingsOf(COMPARED, "1");
        assertEquals(Set.of("email", "other"), read.keySet());
        read.forEach((position, reasons) ->
                assertEquals(List.of(RESTRICTED, "rule_tells_nothing_apart"), reasons, position));
    }

    /** What each position is said, a reason once, where an address split at its {@code @} takes
     *  {@code found} on finding the domain and {@code none} on finding none. */
    private static Map<String, List<String>> readingsOf(String found, String none) {
        String model = """
                module demo

                data Email = String
                    invariant String.matches("[^@]+@[^@]+", value)

                behavior f : (email: Email, other: Email) -> Int
                let f (email, other) =
                    match List.get(1, String.split("@", email.value)) with
                        | Some d -> %s
                        | None -> %s
                """.formatted(found, none);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        ACompiledModel.compiles(compilation);
        JsonNode report = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        Map<String, Set<String>> said = new LinkedHashMap<>();
        collect(report, said);
        Map<String, List<String>> out = new LinkedHashMap<>();
        said.forEach((position, reasons) -> out.put(position, List.copyOf(reasons)));
        return out;
    }

    private static void collect(JsonNode node, Map<String, Set<String>> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason") && node.has("position")) {
            out.computeIfAbsent(node.path("position").asString(), _ -> new TreeSet<>())
                    .add(node.path("reason").asString());
        }
        node.forEach(child -> collect(child, out));
    }
}
