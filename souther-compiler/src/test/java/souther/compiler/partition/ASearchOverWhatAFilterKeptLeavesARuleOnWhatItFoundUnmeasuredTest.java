package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Searching what a filter kept, rather than every candidate, for the first whose number is not a
 * given one costs a rule about what the search found its measure, where the rule reads a value
 * of what was found: the rule is about a derived value, and its lines are not drawn. Whatever the
 * value is held in — a field of a record built of it, or what was found itself — and only for a
 * rule reading a value of it: one comparing what was found against a constant costs nothing,
 * and neither does any rule where the search goes through every candidate.
 *
 * <p>So what is traded for the fewer cases of the staged search is told by the rule and not by
 * the record: the record billing's rule reads is no part of why.
 */
class ASearchOverWhatAFilterKeptLeavesARuleOnWhatItFoundUnmeasuredTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String EVERY_CANDIDATE = """
            List.find(d -> Int.floorMod(d, 7) >= 1 && Int.floorMod(d, 7) <= 5
                    && Bool.not(d == h), List.map(k -> base + k, [0, 1, 2]))""";

    private static final String WHAT_A_FILTER_KEPT = """
            List.find(d -> Bool.not(d == h), List.filter(d -> Int.floorMod(d, 7) >= 1
                    && Int.floorMod(d, 7) <= 5, List.map(k -> base + k, [0, 1, 2])))""";

    /** The rule compares a value of what was found, held in a field of a record built of it. */
    private static final String ITS_WEEKDAY_IN_A_RECORD = """
            {
                let v = V { nominal = base, landed = first(base, h) }
                Bool.not(Int.floorMod(v.landed, 7) >= 1 && Int.floorMod(v.landed, 7) <= 5)
            }""";

    /** The same value, of what was found itself. */
    private static final String ITS_WEEKDAY = """
            Bool.not(Int.floorMod(first(base, h), 7) >= 1
                    && Int.floorMod(first(base, h), 7) <= 5)""";

    /** What was found, against a constant. */
    private static final String WHAT_WAS_FOUND = "first(base, h) > 2";

    /**
     * Where a report says a rule about a derived value was not read: the positions, and how many
     * rules of {@code g}.
     */
    private record Unmeasured(Set<String> at, int rules) {

        static final Unmeasured NOTHING = new Unmeasured(Set.of(), 0);
    }

    /** What the report gives a rule about a derived value as why it was not drawn at. */
    private static Unmeasured aboutADerivedValue(String search, String rule) {
        String source = """
                module demo exposing (g, V)

                data V = { nominal: Int, landed: Int }

                let first (base: Int, h: Int): Int = Option.withDefault(base, SEARCH)

                behavior g : (base: Int, h: Int) -> Bool
                let g (base, h) = RULE
                """.replace("SEARCH", search.indent(4).strip())
                .replace("RULE", rule.indent(4).strip());
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), source);
        JsonNode notRead = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)))
                .path("modules").get(0).path("behaviors").get(0).path("partition")
                .path("notRead");
        Set<String> at = new TreeSet<>();
        Set<JsonNode> rules = new HashSet<>();
        for (JsonNode each : notRead) {
            if (each.path("reason").asString().equals("rule_about_a_derived_value")) {
                assertEquals("g", each.path("ruleId").path("definition").asString(),
                        "a rule of the behavior: " + each);
                at.add(each.path("position").asString());
                rules.add(each.path("ruleId"));
            }
        }
        return new Unmeasured(at, rules.size());
    }

    @Test
    void aRuleReadingAValueOfWhatWasFoundIsLeftUnmeasuredRecordOrNot() {
        Unmeasured inARecord = aboutADerivedValue(WHAT_A_FILTER_KEPT, ITS_WEEKDAY_IN_A_RECORD);
        assertEquals(new Unmeasured(Set.of("base", "h"), 2), inARecord,
                "both comparisons of the weekday found, at every position what was found reads");
        assertEquals(inARecord, aboutADerivedValue(WHAT_A_FILTER_KEPT, ITS_WEEKDAY),
                "and the same where the value is read of what was found itself");
    }

    @Test
    void neitherARuleOnWhatWasFoundNorASearchOfEveryCandidateCostsIt() {
        assertEquals(Unmeasured.NOTHING, aboutADerivedValue(WHAT_A_FILTER_KEPT, WHAT_WAS_FOUND),
                "what was found against a constant is no derived value");
        for (String rule : List.of(ITS_WEEKDAY_IN_A_RECORD, ITS_WEEKDAY, WHAT_WAS_FOUND)) {
            assertEquals(Unmeasured.NOTHING, aboutADerivedValue(EVERY_CANDIDATE, rule),
                    "a search of every candidate leaves the rule its measure: " + rule);
        }
    }
}
