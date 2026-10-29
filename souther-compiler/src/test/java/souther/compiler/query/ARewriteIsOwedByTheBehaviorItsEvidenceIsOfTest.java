package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a behavior is owed of the rewrites of what it calls does not depend on whether another
 * behavior calls the same.
 *
 * <p>Everything that shows a rewrite changes nothing is read of one behavior: the paths to its
 * walks, the rows that ran it, the arms nothing arrives at in it, the lists its calls hand. A
 * helper's fold or fork written once stands in every behavior that calls it, as many places as
 * there are calls, and the rewrite is the one construct. So each behavior is asked about the
 * places it has, and what a behavior owes is what the same behavior owes with the other taken
 * away.
 */
class ARewriteIsOwedByTheBehaviorItsEvidenceIsOfTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** What the behavior is asked of the rewrites, as the document says: the construct, which
     *  rewrite, how it stands. */
    private static List<String> owedBy(Compilation compilation, String behavior) {
        List<String> out = new ArrayList<>();
        for (JsonNode each : JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors")) {
            if (!each.get("name").asString().equals(behavior) || !each.has("replacement")) {
                continue;
            }
            for (JsonNode obligation : each.get("replacement").get("obligations")) {
                JsonNode id = obligation.get("obligationId");
                out.add((id.has("definition") ? id.get("definition").asString() + " " : "")
                        + id.get("rewrite").asString() + ": "
                        + obligation.get("disposition").asString());
            }
        }
        return out;
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }

    /**
     * One module's parts: its head, the signature of each behavior, the helper both call, and the
     * body and rows of each. {@code narrow} is the behavior measured beside {@code wide}, which is
     * the one added.
     */
    private record Model(String head, String narrowSignature, String wideSignature,
                         String helper, String narrow, String wide) {

        String alone() {
            return head + narrowSignature + "\n" + helper + narrow;
        }

        String beside() {
            return head + narrowSignature + wideSignature + "\n" + helper + narrow + wide;
        }

        List<String> owedAlone() {
            return owedBy(measured(alone()), "narrow");
        }

        List<String> owedBeside() {
            return owedBy(measured(beside()), "narrow");
        }
    }

    private static void assertNarrowIsOwedAsIfAlone(Model model) {
        assertEquals(model.owedAlone(), model.owedBeside(),
                "the behavior owes the same whether or not another calls the helper");
    }

    private static final String FOLD_HELPER = """
            let sum (zs: List<Int>) = List.fold((acc, x) -> acc + x, 0, zs)

            """;

    private static final Model THE_LIST_IS_LIMITED_BY_THE_TYPE = new Model("""
            module repro.shared

            data Few = List<Int>
                invariant atMost = List.length(value) <= 1

            """,
            "behavior narrow : (xs: Few) -> Int\n",
            "behavior wide : (xs: List<Int>) -> Int\n",
            FOLD_HELPER, """
            let narrow (xs) = sum(xs.value)

            example narrow
                | "empty" : (Few([])) -> 0
                | (Few([5])) -> 5

            """, """
            let wide (xs) = sum(xs)

            example wide
                | ([]) -> 0
                | ([5]) -> 5
            """);

    /** The fold is the same under either spelling for the behavior whose list is limited. */
    @Test
    void aFoldTheListsOfOneBehaviorLimitIsNotOwedBecauseAnotherCallsItWithAnyList() {
        assertEquals(List.of(), foldsOnly(THE_LIST_IS_LIMITED_BY_THE_TYPE.owedAlone()));
        assertNarrowIsOwedAsIfAlone(THE_LIST_IS_LIMITED_BY_THE_TYPE);
    }

    /** And it is owed by the one whose list is not limited, as it was. */
    @Test
    void theBehaviorWhoseListIsNotLimitedIsOwedTheFoldStill() {
        List<String> wide = owedBy(measured(THE_LIST_IS_LIMITED_BY_THE_TYPE.beside()), "wide");

        assertEquals(2, foldsOnly(wide).size(), wide::toString);
    }

    private static List<String> foldsOnly(List<String> owed) {
        return owed.stream().filter(each -> each.contains("fold_")).toList();
    }

    private static final Model THE_WAY_THAT_PARTS_AN_ARM_IS_RULED_OUT = new Model("""
            module repro.fork

            data Small = Int
                invariant value <= 50

            """,
            "behavior narrow : (p: Small) -> Int\n",
            "behavior wide : (n: Int) -> Int\n", """
            let grade (n: Int) = if n > 0 then (if n > 100 then 2 else 1) else 1

            """, """
            let narrow (p) = grade(p.value)

            example narrow
                | (Small(3)) -> 1
                | (Small(0 - 1)) -> 1

            """, """
            let wide (n) = grade(n)

            example wide
                | (3) -> 1
                | (0 - 1) -> 1
            """);

    /** A sibling of an arm that parts from it only inside an arm nothing arrives at in one
     *  behavior is not owed there because another behavior can arrive there. */
    @Test
    void anArmTheWaysOfOneBehaviorRuleOutIsNotOwedBecauseAnotherCanArriveThere() {
        assertNarrowIsOwedAsIfAlone(THE_WAY_THAT_PARTS_AN_ARM_IS_RULED_OUT);
    }

    /**
     * What a search for a row is asked under when it chooses a row of the behavior is what the
     * measure owes the behavior, with another calling the helper or not.
     */
    @Test
    void theRewritesARowIsChosenUnderDoNotDependOnWhetherAnotherBehaviorCallsTheHelper() {
        Model model = THE_LIST_IS_LIMITED_BY_THE_TYPE;
        int alone = ComposedRows.rewritesThrough(
                measured(model.alone()), "narrow", "empty").size();
        int beside = ComposedRows.rewritesThrough(
                measured(model.beside()), "narrow", "empty").size();

        assertEquals(0, alone);
        assertEquals(alone, beside);
    }

    /** The arm model owes something alone, so the comparison above is of something. */
    @Test
    void theArmModelOwesSomethingAlone() {
        assertFalse(THE_WAY_THAT_PARTS_AN_ARM_IS_RULED_OUT.owedAlone().isEmpty());
    }
}
