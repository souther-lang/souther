package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.About;
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
 * A rule of a decision read short is said of that rule, on every surface, and the rules beside it
 * are reported as what the rows established.
 *
 * <p>Two facts about how a decision was read and they are not one. A reading that stopped has not
 * got the rules, which is about the list; a rule read short is a rule the reading has and described
 * by less than it turns on, which is about that entry. Said as a fact about the list, a page stops
 * before the rules it does have and a document cannot say which rule was short.
 *
 * <p>The body below reads one way short: the {@code then} of a condition that settles one
 * comparison both ways is a way the reading of the rules cannot write down, and the way through the
 * {@code else} of the same fork is read in full. The rows take the first rule and leave the last,
 * which is the gap a reader is owed.
 */
class ARuleReadShortIsSaidOfThatRuleOnEverySurfaceTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module demo
            data Yes
            data No
            data Big
            behavior pick : (n: Int) -> Yes | No | Big
            let pick (n) = if n > 10 then Big else (if n > 3 && n <= 3 then Yes else No)
            example pick
                | (11) -> Big
                | (5) -> No
            """;

    /**
     * The finding about the rule read in full is the gap, and nothing about the rule read short is.
     *
     * <p>Whether the rule read short is owed a row at all is the model's answer, and here it is not;
     * what a finding about such a rule comes to where there is one is
     * {@code ARuleReadShortOfItsWayIsTakenByNoRunTest}'s.
     */
    @Test
    void theRuleBesideTheOneReadShortIsStillTheGapTheRowsEstablished() {
        List<String> said = new ArrayList<>();
        for (Adequacy.Finding each : measured().db().ask(new Adequacy.DecisionFindings("demo"))
                .value()) {
            if (each.about() instanceof About.ARuleNoRowTakes rule) {
                said.add((rule.ruled().whole() ? "whole " : "short ")
                        + (each.isAdequacyGap() ? "gap" : each.disposition().name()));
            }
        }
        assertTrue(said.contains("whole gap"),
                () -> "a rule read in full that no row takes is a gap: " + said);
        assertFalse(said.contains("short gap"),
                () -> "and no rule read short is one: " + said);
    }

    /** The page writes the rules and the gap, and does not say the rules were not read. */
    @Test
    void thePageWritesTheRulesAndDoesNotSayTheListWasNotRead() {
        Compilation measured = measured();
        String page = AdequacyReport.of(measured)
                .human(SourceRendering.namedByIdentity(measured.texts()));
        assertFalse(page.contains("decision    not fully read"),
                () -> "the list of rules was read whole:\n" + page);
        assertTrue(page.contains("no row takes a decision rule"),
                () -> "and the rule no row takes is on the page:\n" + page);
    }

    /**
     * The document says which rule was read short, on that entry and on no other, and says nothing
     * about the list.
     */
    @Test
    void theDocumentSaysWhichRuleWasReadShort() {
        Compilation measured = measured();
        JsonNode document = JSON.readTree(AdequacyReport.of(measured)
                .json(SourceRendering.namedByIdentity(measured.texts())));
        EveryObjectThisWritesIsShapedTheWayTheSchemaSaysTest.assertShapedLikeTheSchema(document);

        JsonNode decision = document.get("modules").get(0).get("behaviors").get(0).get("decision");
        assertFalse(decision.has("weakening"),
                () -> "the list of rules went without nothing: " + decision);
        assertTrue(words(decision.get("coverage")).contains("decision_rule_read_short"),
                () -> "and the measure of all of them is short of one: " + decision);
        List<String> entries = new ArrayList<>();
        for (JsonNode one : decision.get("obligations")) {
            entries.add(String.join(",", words(one)));
        }
        assertEquals(1, entries.stream().filter("decision_rule_read_short"::equals).count(),
                () -> "one entry is the rule read short: " + entries);
        assertEquals(entries.size() - 1, entries.stream().filter(String::isEmpty).count(),
                () -> "and every other entry went without nothing: " + entries);
    }

    private static List<String> words(JsonNode of) {
        List<String> out = new ArrayList<>();
        if (of.has("weakening")) {
            of.get("weakening").forEach(each -> out.add(each.asString()));
        }
        return out;
    }

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
