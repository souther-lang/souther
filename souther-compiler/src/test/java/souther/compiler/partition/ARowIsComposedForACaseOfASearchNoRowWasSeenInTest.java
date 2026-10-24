package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A step of a search no row was seen in is a case a row can be composed for, and the row that comes
 * back is one whose run was seen in it.
 *
 * <p>The rules of the decision are not what is short: they are all in hand. What the rows leave
 * unmeasured is inside the rule that takes the search, so the way to the rule is composed with what
 * the case asks of the node the search starts at, and kept only where the run says it was evidence
 * of the case.
 */
class ARowIsComposedForACaseOfASearchNoRowWasSeenInTest {

    private static final String SOME = """
            module m
            data Node = { v: Int, below: List<Node> }
            data Yes
            data No
            let anyBig (n: Node): Bool = n.v > 5 || List.any(c -> anyBig(c), n.below)
            behavior f : (t: Node) -> Yes | No
            let f (t) = if anyBig(t) then Yes else No
            """;

    private static final String ROWS_THAT_FIND = """
            example f
                | "the top" : (Node { v = 9, below = [] }) -> Yes
                | "below" : (Node { v = 0, below = [ Node { v = 9, below = [] } ] }) -> Yes
            """;

    @Test
    void theStepsOfAnEmptySearchNoRowWasSeenInAreComposed() {
        Map<CaseOfAStatement, RowToRun> found = search(SOME + ROWS_THAT_FIND);
        assertEquals(Set.of(CaseOfAStatement.Step.NOWHERE_AT_A_LEAF,
                CaseOfAStatement.Step.NOWHERE_BELOW), stepsOf(found),
                () -> "both ways of coming back empty: " + found.keySet());
        found.forEach((each, row) -> {
            String written = row.inputs().getFirst().text();
            switch (((CaseOfAStatement.Search) each).step()) {
                case NOWHERE_AT_A_LEAF -> assertTrue(written.contains("below = []"),
                        () -> "a node with nothing below: " + written);
                case NOWHERE_BELOW -> assertTrue(!written.startsWith("Node { v = 5, below = [] }")
                        && !written.contains("v = 9"),
                        () -> "a node with something below, none of which finds one: " + written);
                default -> throw new AssertionError("a step no one asked for: " + each);
            }
        });
    }

    @Test
    void aCaseARowWasSeenInIsNotSearchedFor() {
        Map<CaseOfAStatement, RowToRun> found = search(SOME + ROWS_THAT_FIND + """
                    | "a leaf that fails" : (Node { v = 0, below = [] }) -> No
                """);
        assertEquals(Set.of(CaseOfAStatement.Step.NOWHERE_BELOW), stepsOf(found),
                () -> "only the step no row was in: " + found.keySet());
    }

    private static Set<CaseOfAStatement.Step> stepsOf(Map<CaseOfAStatement, RowToRun> found) {
        return found.keySet().stream()
                .map(each -> ((CaseOfAStatement.Search) each).step())
                .collect(Collectors.toSet());
    }

    private static Map<CaseOfAStatement, RowToRun> search(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        DecisionEvidence evidence = compilation.db().ask(new Adequacy.Decides(module)).value()
                .get("f");
        List<CaseOfAStatement> unseen = evidence.took().made().orElseThrow().unseenCases();
        assertTrue(!unseen.isEmpty(), () -> "the rows leave a step unseen: " + evidence.took());
        return compilation.db().ask(new Adequacy.CaseSearch(module, "f")).value();
    }
}
