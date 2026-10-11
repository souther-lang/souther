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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A search of a tree read as some node reachable meeting a statement is two things in the report,
 * and they stay two.
 *
 * <p>What a decision rule is, is the search as a whole: whether some node at any depth meets the
 * statement. Which rule a row takes is what the row comes to when it is run, so a row that only a
 * grandchild settles takes the rule a row settled at the top does. And what the measures over the
 * input's positions read is as deep as a row is written and no deeper: the nodes under the top are
 * a place nothing read, said as such, so a search read whole is never what makes a behavior's
 * measurement complete.
 */
class WhatASearchDecidesIsTakenByTheRowsThatRunItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String DECLARATIONS = """
            module m
            data Node = { v: Int, below: List<Node> }
            data Yes
            data No
            let anyBig (n: Node): Bool = n.v > 5 || List.any(c -> anyBig(c), n.below)
            let allSmall (n: Node): Bool = n.v <= 5 && List.all(c -> allSmall(c), n.below)
            """;

    private static final String SOME = DECLARATIONS + """
            behavior f : (t: Node) -> Yes | No
            let f (t) = if anyBig(t) then Yes else No
            """;

    private static final String EVERY = DECLARATIONS + """
            behavior f : (t: Node) -> Yes | No
            let f (t) = if allSmall(t) then Yes else No
            """;

    @Test
    void aRowOnlyAGrandchildSettlesTakesTheRuleOfSomeNodeMeetingIt() {
        JsonNode f = behavior(SOME + """
                example f
                    | "a grandchild" :
                        (Node { v = 0, below = [ Node { v = 0, below = [ Node { v = 9, below = [] } ] } ] })
                        -> Yes
                """);
        assertEquals(Map.of("held", true, "denied", false), takenByOutcome(f));
    }

    @Test
    void aRowOneOfSeveralChildrenSettlesTakesTheSameRule() {
        JsonNode f = behavior(SOME + """
                example f
                    | "one of two" :
                        (Node { v = 0, below = [ Node { v = 0, below = [] }, Node { v = 9, below = [] } ] })
                        -> Yes
                """);
        assertEquals(Map.of("held", true, "denied", false), takenByOutcome(f));
    }

    @Test
    void theTopMeetingItAndATopWithNothingBelowAreTheTwoRules() {
        JsonNode f = behavior(SOME + """
                example f
                    | "the top" : (Node { v = 9, below = [] }) -> Yes
                    | "nothing below" : (Node { v = 0, below = [] }) -> No
                """);
        assertEquals(Map.of("held", true, "denied", true), takenByOutcome(f));
    }

    @Test
    void aRowOnlyAGrandchildFailsTakesTheRuleOfSomeNodeFailingIt() {
        // Every node small, held where none is big: the rule is about the node that is big.
        JsonNode f = behavior(EVERY + """
                example f
                    | "a grandchild too big" :
                        (Node { v = 0, below = [ Node { v = 0, below = [ Node { v = 9, below = [] } ] } ] })
                        -> No
                """);
        assertEquals(Map.of("held", true, "denied", false), takenByOutcome(f));
    }

    @Test
    void oneSearchFromTwoPositionsIsTwoStatements() {
        JsonNode f = behavior(DECLARATIONS + """
                behavior f : (a: Node, b: Node) -> Yes | No
                let f (a, b) = if anyBig(a) && Bool.not(anyBig(b)) then Yes else No
                example f
                    | "a" : (Node { v = 9, below = [] }, Node { v = 0, below = [] }) -> Yes
                """);
        List<String> stated = new ArrayList<>();
        for (JsonNode obligation : f.get("decision").get("obligations")) {
            for (JsonNode condition : obligation.get("obligationId").get("conditions")) {
                stated.add(condition.get("condition").asString());
            }
        }
        assertTrue(stated.stream().anyMatch(each -> each.startsWith("reachable a from a ")),
                () -> "a search from a: " + stated);
        assertTrue(stated.stream().anyMatch(each -> each.startsWith("reachable b from b ")),
                () -> "a search from b: " + stated);
        assertWentWithoutWhatIsBelow(f, "a.below[*]");
        assertWentWithoutWhatIsBelow(f, "b.below[*]");
    }

    @Test
    void whateverTheRowsTheNodesBelowAreWhatTheMeasureWentWithout() {
        for (String source : List.of(SOME, EVERY, SOME + """
                example f
                    | "the top" : (Node { v = 9, below = [] }) -> Yes
                    | "nothing below" : (Node { v = 0, below = [] }) -> No
                """)) {
            assertWentWithoutWhatIsBelow(behavior(source), "t.below[*]");
        }
    }

    /** That {@code f} is no complete measurement, and says the nodes under {@code below} are why. */
    private static void assertWentWithoutWhatIsBelow(JsonNode f, String below) {
        assertEquals("partial", f.get("status").asString(), () -> "measured as " + f);
        List<String> notRead = new ArrayList<>();
        f.get("partition").get("notRead").forEach(each -> notRead.add(each.get("position").asString()));
        assertTrue(notRead.contains(below), () -> below + " is said to be not read: " + notRead);
        List<String> weakening = new ArrayList<>();
        f.get("weakening").forEach(each -> weakening.add(each.asString()));
        assertTrue(weakening.contains("position_not_read"), () -> "weakened by " + weakening);
    }

    /** Whether the rule of the search coming out each way was taken, by that way. */
    private static Map<String, Boolean> takenByOutcome(JsonNode f) {
        Map<String, Boolean> out = new LinkedHashMap<>();
        for (JsonNode obligation : f.get("decision").get("obligations")) {
            JsonNode conditions = obligation.get("obligationId").get("conditions");
            assertEquals(1, conditions.size(), () -> "one condition: " + conditions);
            assertTrue(conditions.get(0).get("condition").asString().startsWith("reachable t "),
                    () -> "the search is the condition: " + conditions);
            out.put(conditions.get(0).get("outcome").asString(),
                    obligation.get("taken").asBoolean());
        }
        return out;
    }

    private static JsonNode behavior(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        return JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0);
    }
}
