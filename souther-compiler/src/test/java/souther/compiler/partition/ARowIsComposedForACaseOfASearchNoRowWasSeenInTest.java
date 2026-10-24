package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

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

    /**
     * What the way writes of the start node does not decide the children, so a candidate whose
     * children meet the search is composed for the case all the same. Its run says it is not in
     * the case, and no row outside it is offered: not finding one is what this compiler composed,
     * and a row for the wrong case is a row the author is told to write.
     */
    @Test
    void aCandidateWhoseChildrenMeetTheSearchIsNeverOfferedForTheCaseTheyAreNotIn() {
        Map<CaseOfAStatement, RowToRun> found = search("""
                module m
                data Node = { v: Int, below: List<Node> }
                data Yes
                data No
                let anyLow (n: Node): Bool = n.v < 3 || List.any(c -> anyLow(c), n.below)
                behavior f : (t: Node) -> Yes | No
                let f (t) = if anyLow(t) then Yes else No
                example f
                    | "the top" : (Node { v = 1, below = [] }) -> Yes
                    | "below" : (Node { v = 5, below = [ Node { v = 1, below = [] } ] }) -> Yes
                """);
        assertTrue(!stepsOf(found).contains(CaseOfAStatement.Step.NOWHERE_BELOW),
                () -> "no row of this is in the case: " + found.keySet());
        assertTrue(stepsOf(found).contains(CaseOfAStatement.Step.NOWHERE_AT_A_LEAF),
                () -> "and the step a candidate is in is still found: " + found.keySet());
    }

    @Test
    void aCaseARowWasSeenInIsNotSearchedFor() {
        Map<CaseOfAStatement, RowToRun> found = search(SOME + ROWS_THAT_FIND + """
                    | "a leaf that fails" : (Node { v = 0, below = [] }) -> No
                """);
        assertEquals(Set.of(CaseOfAStatement.Step.NOWHERE_BELOW), stepsOf(found),
                () -> "only the step no row was in: " + found.keySet());
    }

    @Test
    void theBlockOffersARowForEachStepNoRowWasSeenIn() {
        String block = blockOf(SOME + ROWS_THAT_FIND);
        assertTrue(block.contains("a search that finds nothing at a node with nothing below it"),
                () -> "a row for the leaf: " + block);
        assertTrue(block.contains("a search that finds nothing through the nodes below its start"),
                () -> "a row for the children: " + block);
    }

    @Test
    void theBlockOffersNoRowForAStepARowWasSeenIn() {
        String block = blockOf(SOME + ROWS_THAT_FIND + """
                    | "a leaf that fails" : (Node { v = 0, below = [] }) -> No
                """);
        assertTrue(!block.contains("a search that finds nothing at a node with nothing below it"),
                () -> "the leaf is already written: " + block);
        assertTrue(block.contains("a search that finds nothing through the nodes below its start"),
                () -> "the children are not: " + block);
    }

    private static String blockOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule(module)),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
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
