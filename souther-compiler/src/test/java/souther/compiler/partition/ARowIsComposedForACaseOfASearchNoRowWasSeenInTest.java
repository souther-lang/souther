package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.RowWork;
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

    /**
     * A case no row was seen in is work the offer in front of the behavior knows of.
     *
     * <p>Where nothing else is owed, the cases are all there is: the classes are covered, both
     * rules are taken, and the editor decides whether to offer the rows by what is owed. Left out
     * of it, the command printed a row the editor never offered.
     */
    @Test
    void aCaseIsTheOnlyWorkOwedAndTheOfferKnowsOfIt() {
        Compilation compilation = Compilation.ofSource(SOME + ROWS_THAT_FIND + """
                    | "a child that fails" :
                        (Node { v = 0, below = [ Node { v = 0, below = [] } ] }) -> No
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        RowWork owed = compilation.db().ask(new Adequacy.RowsOwed(module, "f")).value();

        assertEquals(List.of(), owed.rules(), "both rules are taken");
        assertEquals(List.of(), owed.classes(), "and no class is owed");
        assertEquals(List.of(), owed.arms(), "and no arm");
        assertEquals(Set.of(CaseOfAStatement.Step.NOWHERE_AT_A_LEAF),
                owed.cases().stream().map(each -> ((CaseOfAStatement.Search) each).step())
                        .collect(Collectors.toSet()),
                "the leaf is the one step no row was seen in");
        assertTrue(!owed.isEmpty(), "so there is work the offer stands for");
    }

    /**
     * Finding a node below the start is composed for with a start that does not meet the search
     * and has something below it; the run says whether a child does.
     */
    @Test
    void theStepThatFindsOneBelowTheStartIsComposedAndItsRowFindsOne() {
        Map<CaseOfAStatement, RowToRun> found = search(SOME + """
                example f
                    | "the top" : (Node { v = 9, below = [] }) -> Yes
                    | "a leaf that fails" : (Node { v = 0, below = [] }) -> No
                    | "a child that fails" :
                        (Node { v = 0, below = [ Node { v = 0, below = [] } ] }) -> No
                """);
        assertEquals(Set.of(CaseOfAStatement.Step.BELOW_IT), stepsOf(found),
                () -> "the one step no row was seen in: " + found.keySet());
        String written = found.values().iterator().next().inputs().getFirst().text();
        assertTrue(written.contains("below = [Node {") && !written.startsWith("Node { v = 9"),
                () -> "a start with a child, whose run found one below: " + written);
    }

    @Test
    void theBlockOffersARowForTheStepThatFindsOneBelowTheStart() {
        String block = blockOf(SOME + """
                example f
                    | "the top" : (Node { v = 9, below = [] }) -> Yes
                    | "a leaf that fails" : (Node { v = 0, below = [] }) -> No
                    | "a child that fails" :
                        (Node { v = 0, below = [ Node { v = 0, below = [] } ] }) -> No
                """);
        assertTrue(block.contains("a search that finds what it asks below the node it starts at"),
                () -> "a row for the step below the start: " + block);
    }

    /**
     * Finding one below is a node at some depth, and the rules may leave room at one depth only:
     * where every child must fail the search, the node it finds is a grandchild.
     */
    @Test
    void theStepBelowTheStartIsLookedForDeeperWhereTheRulesKeepEveryChildFromMeetingIt() {
        Map<CaseOfAStatement, RowToRun> found = search("""
                module m
                data Node = { v: Int, below: List<Node> }
                data Yes
                data No
                let anyBig (n: Node): Bool = n.v > 5 || List.any(c -> anyBig(c), n.below)
                behavior f : (t: Node) -> Yes | No
                let f (t) = if List.all(c -> c.v <= 5, t.below) && anyBig(t) then Yes else No
                example f
                    | "the top" : (Node { v = 9, below = [] }) -> Yes
                    | "a leaf that fails" : (Node { v = 0, below = [] }) -> No
                """);
        assertEquals(Set.of(CaseOfAStatement.Step.BELOW_IT), stepsOf(found),
                () -> "the step is composed at the depth the rule leaves room at: "
                        + found.keySet());
        String written = found.values().iterator().next().inputs().getFirst().text();
        assertTrue(written.chars().filter(c -> c == '[').count() >= 3
                        && written.contains("below = [Node { v = ")
                        && written.indexOf("below = [Node", written.indexOf("below = [Node") + 1)
                        > 0,
                () -> "a node two levels down: " + written);
    }

    /**
     * A number that is none where the search's condition is moved to a node below is no reason to
     * stop: the step has nothing that steers a row to a node below, so it is not offered, and the
     * other steps are looked for as before.
     */
    @Test
    void aConditionThatCannotBeMovedBelowTheStartLeavesTheOtherStepsSearched() {
        Map<CaseOfAStatement, RowToRun> found = search("""
                module m
                data Node = { xs: List<Int>, below: List<Node> }
                data Yes
                data No
                let anyBig (n: Node): Bool =
                    List.sum(List.map(x -> x * 2, n.xs)) > 5 || List.any(c -> anyBig(c), n.below)
                behavior f : (t: Node) -> Yes | No
                let f (t) = if anyBig(t) then Yes else No
                example f
                    | "the top" : (Node { xs = [9], below = [] }) -> Yes
                """);
        assertTrue(!stepsOf(found).contains(CaseOfAStatement.Step.BELOW_IT),
                () -> "nothing steers a row below the start: " + found.keySet());
        assertTrue(stepsOf(found).contains(CaseOfAStatement.Step.NOWHERE_AT_A_LEAF),
                () -> "and the steps that need no node below are searched: " + found.keySet());
    }

    /**
     * Only the step below the start reads places inside the nodes below: a search asked for the
     * ways of coming back empty builds against the reading the measurement was made against.
     */
    @Test
    void aStepThatAsksNothingInsideTheNodesBelowReadsNoPlaceThere() {
        Compilation compilation = Compilation.ofSource(SOME + ROWS_THAT_FIND, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        DecisionEvidence evidence = compilation.db().ask(new Adequacy.Decides(module)).value()
                .get("f");
        List<CaseOfAStatement.Search> unseen = evidence.took().made().orElseThrow().unseenCases()
                .stream().map(CaseOfAStatement.Search.class::cast).toList();
        assertTrue(!unseen.isEmpty(), "the empty steps are unseen");
        InputDomain measured = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertTrue(unseen.stream().allMatch(each ->
                        CaseCandidates.OF_THE_SEARCH.placesToBuildFor(each, measured).isEmpty()),
                () -> "no place below is read for " + unseen);
    }

    /**
     * Looking for a row reads the input of its own and leaves the measurement's alone: the
     * positions the measure counts are the same after a search as before it.
     */
    @Test
    void lookingForTheStepBelowTheStartLeavesThePositionsTheMeasureCountsAlone() {
        Compilation compilation = Compilation.ofSource(SOME + """
                example f
                    | "the top" : (Node { v = 9, below = [] }) -> Yes
                    | "a leaf that fails" : (Node { v = 0, below = [] }) -> No
                    | "a child that fails" :
                        (Node { v = 0, below = [ Node { v = 0, below = [] } ] }) -> No
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        List<String> before = positionsOf(compilation, module);
        assertTrue(!compilation.db().ask(new Adequacy.CaseSearch(module, "f")).value().isEmpty(),
                "a row is found for the step");
        assertEquals(before, positionsOf(compilation, module));
        assertTrue(before.stream().noneMatch(each -> each.contains("below[*].v")),
                () -> "the measurement stops where the type returns to itself: " + before);
    }

    /**
     * A place whose rules some value names is not a place the reading read. The element of a
     * container on the edge of a recursive type is named by its own rules and has no position, so
     * the measurement makes no way to a step that asks something there, and the ways to it are the
     * ones of a reading made to read the places.
     */
    @Test
    void theMeasurementMakesNoWayAtAPlaceItDidNotRead() {
        Compilation compilation = Compilation.ofSource(SOME + ROWS_THAT_FIND, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        InputDomain measured = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        TermPath below = TermPath.of("t").then("below").element().then("v");

        assertTrue(!measured.ruleRoots().naming(below).isEmpty(),
                "the rules of an element name the place");
        assertTrue(!CaseCandidates.reads(measured, below), "and no position was read there");
        DecisionReading decision = compilation.db().ask(new Adequacy.Decides(module)).value()
                .get("f").read();
        assertTrue(decision.stated().stream().flatMap(each -> each.occurrences().stream())
                        .flatMap(each -> each.caseWays().stream())
                        .noneMatch(each -> each.which() instanceof CaseOfAStatement.Search search
                                && search.step() == CaseOfAStatement.Step.BELOW_IT),
                "so no way asks anything of a node below");
    }

    private static List<String> positionsOf(Compilation compilation, String module) {
        return compilation.db().ask(new Adequacy.Inputs(module)).value().get("f").positions()
                .stream().map(each -> each.toString()).toList();
    }

    /**
     * A search down two fields has no one field to move what it asks to, so nothing steers a row
     * to a node below and the step is no work: it stays reported as unmeasured and is not offered.
     */
    @Test
    void aStepBelowTheStartOfASearchDownTwoFieldsIsNoWork() {
        Compilation compilation = Compilation.ofSource("""
                module m
                data Tree = { v: Int, left: List<Tree>, right: List<Tree> }
                data Yes
                data No
                let anyBig (n: Tree): Bool =
                    n.v > 5 || List.any(c -> anyBig(c), n.left) || List.any(c -> anyBig(c), n.right)
                behavior f : (t: Tree) -> Yes | No
                let f (t) = if anyBig(t) then Yes else No
                example f
                    | "the top" : (Tree { v = 9, left = [], right = [] }) -> Yes
                    | "a leaf that fails" : (Tree { v = 0, left = [], right = [] }) -> No
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        DecisionEvidence evidence = compilation.db().ask(new Adequacy.Decides(module)).value()
                .get("f");
        assertTrue(evidence.took().made().orElseThrow().unseenCases().stream().anyMatch(
                        each -> each instanceof CaseOfAStatement.Search search
                                && search.step() == CaseOfAStatement.Step.BELOW_IT),
                "the step is owed and no row was seen in it");
        RowWork owed = compilation.db().ask(new Adequacy.RowsOwed(module, "f")).value();
        assertTrue(owed.cases().stream().noneMatch(each -> each instanceof CaseOfAStatement.Search
                        search && search.step() == CaseOfAStatement.Step.BELOW_IT),
                () -> "no row is looked for below the start: " + owed.cases());
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
