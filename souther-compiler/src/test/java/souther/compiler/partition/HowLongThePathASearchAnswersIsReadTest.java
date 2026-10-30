package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.Carrier;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PlacesMoved;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How long the line is that a search down a tree answers is read as a number of the tree it goes
 * down and the value it is for: the search stops at the first node, in the order it goes down,
 * that holds the value, and answers that node and each node above it. Where the body is anything
 * else — it keeps the answer of the last element rather than the first, asks the nodes below
 * before the node, puts more than the node in the list, or asks anything but that one equality —
 * the length is not read, and nothing is made up for it.
 */
class HowLongThePathASearchAnswersIsReadTest {

    private static final String DECLARATIONS = """
            module demo

            data Node = { v: Int, d: Decimal, k: Int, below: List<Node>, other: List<Node> }
            data In = { t: Node, ts: List<Node>, w: Int, x: Decimal, k: Int }
            """;

    private static final String PATH_TO = """
            let pathTo (node: Node, w: Int): List<Int> =
                if node.v == w
                    then [ node.v ]
                    else {
                        let below = List.fold((found, r) ->
                                if List.isEmpty(found) then pathTo(r, w) else found,
                            [], node.below)
                        if List.isEmpty(below) then [] else [ node.v ] ++ below
                    }
            """;

    private static final TermPath T = TermPath.of("i").then("t");
    private static final TermPath W = TermPath.of("i").then("w");

    private static final RunSource.SearchedLine LINE =
            new RunSource.SearchedLine(T, "below", List.of("v"), W);

    @Test
    void theLengthOfALineIsHowManyNodesTheSearchFindsOnTheWayToTheValue() {
        assertEquals(Map.of(LINE, ExactRatio.ONE), linesIn(stated(PATH_TO,
                "List.length(pathTo(i.t, i.w)) >= i.k")));
    }

    @Test
    void theNodesOfTheLineAreCountedWhateverIsDoneToTheListAfterwards() {
        assertEquals(Map.of(LINE, ExactRatio.ONE), linesIn(stated(PATH_TO,
                "List.length(List.reverse(pathTo(i.t, i.w))) >= i.k")));
        // Dropping one is nought where the line is nought and one fewer otherwise, which is two
        // cases of the same number.
        Proposition dropped = stated(PATH_TO,
                "List.length(List.drop(1, List.reverse(pathTo(i.t, i.w)))) >= i.k");
        assertFalse(Proposition.leavesSomethingUnread(dropped), () -> "read as " + dropped);
        assertTrue(dropped.key().contains(LINE.toString()), () -> "read as " + dropped);
    }

    /** The search is for a value the rule names, so another field and another input are another
     *  line. */
    @Test
    void theFieldAndTheValueSearchedForAreThoseTheBodyAsks() {
        String byTheOtherField = PATH_TO.replace("node.v == w", "node.k == w");
        assertEquals(Map.of(new RunSource.SearchedLine(T, "below", List.of("k"), W),
                ExactRatio.ONE),
                linesIn(stated(byTheOtherField, "List.length(pathTo(i.t, i.w)) >= i.k")));
        assertEquals(Map.of(new RunSource.SearchedLine(T, "below", List.of("v"),
                TermPath.of("i").then("k")), ExactRatio.ONE),
                linesIn(stated(PATH_TO, "List.length(pathTo(i.t, i.k)) >= i.w")));
    }

    /** The tree is the field the fold goes down, and the field is part of which line it is. */
    @Test
    void theFieldTheSearchGoesDownIsPartOfTheLine() {
        String throughTheOther = PATH_TO.replace("node.below", "node.other");
        assertEquals(Map.of(new RunSource.SearchedLine(T, "other", List.of("v"), W),
                ExactRatio.ONE),
                linesIn(stated(throughTheOther, "List.length(pathTo(i.t, i.w)) >= i.k")));
    }

    @Test
    void aSearchThatKeepsTheAnswerOfTheLastElementIsNotTheLineToTheFirstNode() {
        assertUnread(stated(PATH_TO.replace(
                "if List.isEmpty(found) then pathTo(r, w) else found", "pathTo(r, w)"),
                "List.length(pathTo(i.t, i.w)) >= i.k"));
    }

    @Test
    void aSearchThatAsksTheNodesBelowBeforeTheNodeIsNotTheLineToTheFirstNode() {
        assertUnread(stated("""
                let pathTo (node: Node, w: Int): List<Int> = {
                    let below = List.fold((found, r) ->
                            if List.isEmpty(found) then pathTo(r, w) else found,
                        [], node.below)
                    if List.isEmpty(below)
                        then (if node.v == w then [ node.v ] else [])
                        else [ node.v ] ++ below
                }
                """, "List.length(pathTo(i.t, i.w)) >= i.k"));
    }

    @Test
    void aSearchThatListsMoreThanTheNodeIsNotACountOfTheNodes() {
        assertUnread(stated(PATH_TO.replace("[ node.v ] ++ below", "[ node.v, node.v ] ++ below"),
                "List.length(pathTo(i.t, i.w)) >= i.k"));
        assertUnread(stated(PATH_TO.replace("then [ node.v ]", "then [ node.v, node.v ]"),
                "List.length(pathTo(i.t, i.w)) >= i.k"));
    }

    @Test
    void aSearchThatAsksAnythingButOneEqualityOfTheNodeIsNotRead() {
        assertUnread(stated(PATH_TO.replace("node.v == w", "node.v > w"),
                "List.length(pathTo(i.t, i.w)) >= i.k"));
        assertUnread(stated(PATH_TO.replace("node.v == w", "node.v == w && node.k > 0"),
                "List.length(pathTo(i.t, i.w)) >= i.k"));
    }

    /** What a node is asked against has to stay put, and not be another node's own field. */
    @Test
    void aValueThatIsAFieldOfTheTreeIsNoValueSearchedFor() {
        assertUnread(stated(PATH_TO, "List.length(pathTo(i.t, i.t.v)) >= i.k"));
    }

    /** A decimal's two spellings of one value are one value in the language and two in a row. */
    @Test
    void aValueTheRowSpellsMoreThanOneWayIsNotComparedAsItStands() {
        assertUnread(stated("""
                let pathToD (node: Node, x: Decimal): List<Int> =
                    if node.d == x
                        then [ node.v ]
                        else {
                            let below = List.fold((found, r) ->
                                    if List.isEmpty(found) then pathToD(r, x) else found,
                                [], node.below)
                            if List.isEmpty(below) then [] else [ node.v ] ++ below
                        }
                """, "List.length(pathToD(i.t, i.x)) >= i.k"));
    }

    /**
     * One of many trees is no tree: which of them the search went down is not said by the path of
     * all, and a line is the line of one.
     */
    @Test
    void oneTreeOfManyIsNoLine() {
        Proposition stated = stated(PATH_TO,
                "List.all(t -> List.length(pathTo(t, i.w)) >= 2, i.ts)");
        assertFalse(stated.key().contains("line below"), () -> "read as " + stated);
    }

    /** The values of a line are nodes, of which only how many there are is a number. */
    @Test
    void aLineIsNoRunToAddUp() {
        assertNull(NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"), LINE,
                Type.Prim.INT, NewtypeInners.NONE, SYMBOLS));
        assertInstanceOf(NumericTerm.TakenOver.class, NumericTerm.TakenOver.howManyOf(LINE,
                Type.Prim.INT, NewtypeInners.NONE, SYMBOLS));
    }

    @Test
    void aLineMovedInsideAContainerIsNoLine() {
        TermPath every = TermPath.of("i").then("ts").element();
        assertNull(LINE.movedTo(PlacesMoved.by(at -> at.equals(T) ? every : at)));
        assertThrows(IllegalArgumentException.class,
                () -> new RunSource.SearchedLine(every, "below", List.of("v"), W));
        assertThrows(IllegalArgumentException.class,
                () -> new RunSource.SearchedLine(T, "below", List.of("v"), T.then("v")));
    }

    /** The two places a line is read from both move, and the line is the same one where they do. */
    @Test
    void aLineMovedWhereBothItsPlacesGoIsTheLineThere() {
        TermPath tree = TermPath.of("j").then("t");
        TermPath value = TermPath.of("j").then("w");
        assertEquals(new RunSource.SearchedLine(tree, "below", List.of("v"), value),
                LINE.movedTo(PlacesMoved.by(at -> at.equals(T) ? tree : value)));
    }

    // What a row says of a line.

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    private static final NumericTerm.TakenOver COUNT = NumericTerm.TakenOver.howManyOf(LINE,
            Type.Prim.INT, NewtypeInners.NONE, SYMBOLS);

    private static final TermOrders ON = TermOrdersFixtures.itself(COUNT, new Carrier.Whole());

    private static ObservedValue node(long v, ObservedValue... below) {
        Map<String, ObservedValue> fields = new LinkedHashMap<>();
        fields.put("v", new ObservedValue.Integer(v));
        fields.put("below", new ObservedValue.Sequence(List.of(below)));
        return new ObservedValue.Constructed(TypeSymbols.declared(new TypeKey("demo", "Node")),
                fields);
    }

    /** A row writing {@code tree} at the root and {@code value} at the value searched for. */
    private static BorderQuantity.Observation row(ObservedValue tree, ObservedValue value) {
        return new BorderQuantity.Observation() {
            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                if (path.equals(T) && tree != null) {
                    return WalkResult.reached(new ObservationAtPoint.Value(tree));
                }
                if (path.equals(W) && value != null) {
                    return WalkResult.reached(new ObservationAtPoint.Value(value));
                }
                return WalkResult.reached(ObservationAtPoint.WROTE_NOTHING);
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a line is read at its tree and its value: " + path);
            }

            @Override
            public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
                throw new AssertionError("a line is read at its tree and its value: " + container);
            }
        };
    }

    private static WhatATermRead lineOf(ObservedValue tree, long sought) {
        return WhatATermRead.searchedLine(ON, LINE,
                row(tree, new ObservedValue.Integer(sought)));
    }

    private static WhatATermRead.Number nodes(long how) {
        return new WhatATermRead.Number(Count.of(how));
    }

    @Test
    void aRootHoldingTheValueIsALineOfOneWhateverIsBelowIt() {
        assertEquals(nodes(1), lineOf(node(7), 7));
        assertEquals(nodes(1), lineOf(node(7, node(7, node(7))), 7));
    }

    @Test
    void aNodeBelowTheRootHoldingTheValueIsAsDeepAsItIsAndOne() {
        assertEquals(nodes(2), lineOf(node(1, node(7)), 7));
        assertEquals(nodes(3), lineOf(node(1, node(2, node(7))), 7));
        assertEquals(nodes(4), lineOf(node(1, node(2, node(3, node(7)))), 7));
    }

    @Test
    void theNodeTheSearchStopsAtIsTheFirstInTheOrderItGoesDownAndNotTheShallowest() {
        // The first element's subtree is searched before the second element is, so the node at
        // depth three is found and the one at depth two, beside it, is not.
        ObservedValue tree = node(1, node(2, node(7)), node(7));
        assertEquals(nodes(3), lineOf(tree, 7));
    }

    @Test
    void aTreeHoldingTheValueNowhereHasNoLine() {
        assertEquals(nodes(0), lineOf(node(1, node(2), node(3, node(4))), 7));
    }

    @Test
    void aRowThatWroteNoValueToSearchForOrNoTreeHasNoLine() {
        assertEquals(new WhatATermRead.NothingWrittenThere(),
                WhatATermRead.searchedLine(ON, LINE, row(node(1), null)));
        assertEquals(new WhatATermRead.NothingWrittenThere(),
                WhatATermRead.searchedLine(ON, LINE, row(null, new ObservedValue.Integer(1))));
    }

    // What the report says of the positions of a model that asks how long a line is.

    private static final String CHAIN = """
            module demo

            data Node = { v: Int, below: List<Node> }
            data Low
            data Mid
            data Role = Low | Mid
            data Signed = { n: Int }
            data Missing = { w: Int }
            data TooFar = { w: Int }

            %s

            let levels (role: Role): Int =
                match role with
                    | Low -> 1
                    | Mid -> 2

            behavior chain : (root: Node, w: Int, role: Role) -> Signed | Missing | TooFar
                constructs Signed, Missing, TooFar
            let chain (root, w, role) = {
                let line = pathTo(root, w)
                guard Bool.not(List.isEmpty(line)) else Missing { w = w }
                let above = List.drop(1, List.reverse(line))
                guard List.length(above) >= levels(role) else TooFar { w = w }
                Signed { n = List.length(above) }
            }

            let tree = Node { v = 1, below =
                [ Node { v = 2, below = [ Node { v = 3, below = [] } ] }
                , Node { v = 3, below = [] } ] }

            example chain
                | "the first node in the order the search goes down is the deeper one" :
                    (tree, 3, Low) -> Signed { n = 2 }
                | "the root is the line of one, and nobody is above" :
                    (tree, 1, Low) -> TooFar { w = 1 }
                | "one level down" : (tree, 2, Low) -> Signed { n = 1 }
                | "nobody holds it" : (tree, 9, Low) -> Missing { w = 9 }
            """;

    private static final String SEARCH = PATH_TO;

    private static String report(String search) {
        Compilation compilation = Compilation.ofSource(CHAIN.formatted(search), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(),
                "compiles, and every row answers what it says when it is run");
        return AdequacyReport.of(compilation).json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /**
     * The rows are run, so the line the first of them says is two is what the language does, and
     * what is read of that row is that the same two.
     */
    @Test
    void theRowsOfTheModelAreRunAndNoPositionIsAboutAValueMadeFromThem() {
        String json = report(SEARCH);
        assertFalse(json.contains("rule_about_a_derived_value"), json);
        assertTrue(json.contains("searched_line"), json);
    }

    /**
     * A search that goes down the elements from the last is run by the language in that order, so
     * where two elements below hold the value it stops at the later one. The rows say what the
     * language does: the line is two nodes long here, and the one read from the first element
     * would be three.
     */
    @Test
    void aSearchFromTheLastElementIsNotTheLineToTheFirstNode() {
        String fromTheEnd = SEARCH.replace("List.fold((found, r) ->", "List.foldRight((r, found) ->");
        assertTrue(fromTheEnd.contains("foldRight"), fromTheEnd);
        String model = DEEPEST_LINE_MODEL.formatted(fromTheEnd, "")
                .replace("let tree = Node { v = 1, below = [ Node { v = 2, below = [] } ] }",
                        "let tree = Node { v = 1, below = [ Node { v = 2, below = [ Node { v = 3, below = [] } ] }, Node { v = 3, below = [] } ] }")
                .replace("| \"a\" : (tree, 2) -> Yes", "| \"a\" : (tree, 3) -> No")
                .replace(">= 2", ">= 3");
        Compilation compilation = measuredModel(model);
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList());
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        assertFalse(json.contains("searched_line"), humanOf(compilation));
        assertTrue(json.contains("rule_about_a_derived_value"), humanOf(compilation));
    }

    /**
     * A search that asks the nodes below before the node answers the same on every row above, and
     * a different line wherever a node and one below it both hold the value: the line is not read,
     * and the old reason stays.
     */
    @Test
    void aSearchThatAsksTheNodesBelowFirstStillReportsTheValueMadeFromThePosition() {
        String json = report("""
                let pathTo (node: Node, w: Int): List<Int> = {
                    let below = List.fold((found, r) ->
                            if List.isEmpty(found) then pathTo(r, w) else found,
                        [], node.below)
                    if List.isEmpty(below)
                        then (if node.v == w then [ node.v ] else [])
                        else [ node.v ] ++ below
                }
                """);
        assertTrue(json.contains("rule_about_a_derived_value"), json);
        assertFalse(json.contains("searched_line"), json);
    }

    /**
     * The rows are run, and each says what the language does with the tree it writes: the line is
     * two nodes in the first, one in the second and none in the third. The border of the
     * comparison is drawn at two, and a row is read to stand at each of the three points the rows
     * write — which is the reading agreeing with the run, row by row, since a row read at another
     * point would leave that obligation unmet.
     */
    @Test
    void theRowsOfEachLengthStandAtThePointsOfTheBorderTheyWereWrittenFor() {
        String human = humanReportOf(DEEPEST_LINE_MODEL.formatted(SEARCH, ""));
        // Four points are owed, and the three the rows write are met. The fourth is the one above
        // the border, which needs a tree written for a line of three nodes or more.
        assertTrue(human.contains("borders 1   obligations 3/4"), human);
        assertTrue(human.contains("at an IN point"), human);
        assertTrue(human.contains("in 2 < List.length("), human);
        assertFalse(human.contains("at the ON point") || human.contains("at the OFF point")
                || human.contains("at the OUT point"), human);
    }

    private static final String DEEPEST_LINE_MODEL = """
            module demo

            data Node = { v: Int, below: List<Node> }
            data Yes
            data No

            %s

            behavior f : (root: Node, w: Int) -> Yes | No
            let f (root, w) =
                if List.length(pathTo(root, w)) >= 2 then Yes else No

            let tree = Node { v = 1, below = [ Node { v = 2, below = [] } ] }

            example f
                | "a" : (tree, 2) -> Yes
                | "b" : (tree, 1) -> No
                | "c" : (tree, 9) -> No
            %s""";

    /**
     * The row offered for the point above the border is a tree whose search finds a line past two
     * nodes: written back as an example it is run by the language, which answers what a line past
     * the border does, and the point is read to be met by it.
     */
    @Test
    void theRowOfferedAboveTheBorderIsATreeTheSearchFindsALongLineIn() {
        Compilation before = measuredModel(DEEPEST_LINE_MODEL.formatted(SEARCH, ""));
        List<String> offered = Adequacy.offeredFor(before.db(),
                        OfferingRequest.overTheModule("demo"))
                .rowsByBehavior().getOrDefault("f", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
        assertFalse(offered.isEmpty(), () -> "a row is offered: " + humanOf(before));
        // A chain past two nodes: the root holds a node that holds a node.
        assertTrue(offered.stream().anyMatch(row -> row.split("below = \\[Node", -1).length >= 3),
                () -> "offered " + offered);
        StringBuilder written = new StringBuilder();
        int named = 0;
        for (String inputs : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (").append(inputs)
                    .append(") -> Yes\n");
        }
        Compilation after = measuredModel(DEEPEST_LINE_MODEL.formatted(SEARCH, written));
        String human = humanOf(after);
        assertTrue(human.contains("borders 1   obligations 4/4"), human);
        assertEquals(List.of(), after.errors().stream()
                .map(each -> each.diagnostic().code()).toList());
    }

    /**
     * A node that may hold nothing below it has no line past one node, and a row written with a
     * node below it would be one the declarations refuse: the point above the border is not met,
     * and no row is offered for it.
     */
    @Test
    void aNodeThatMayHoldNothingBelowItHasNoRowOfferedForALineBeyondIt() {
        String model = DEEPEST_LINE_MODEL.formatted(SEARCH, "")
                .replace("data Node = { v: Int, below: List<Node> }", """
                        data Node = { v: Int, below: List<Node> }
                            invariant List.length(below) == 0""")
                .replace("let tree = Node { v = 1, below = [ Node { v = 2, below = [] } ] }\n",
                        "let tree = Node { v = 1, below = [] }\n")
                .replace("| \"a\" : (tree, 2) -> Yes", "| \"a\" : (tree, 1) -> No");
        Compilation compilation = measuredModel(model);
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList());
        assertEquals(List.of(), Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("demo"))
                .rowsByBehavior().getOrDefault("f", List.of()).stream()
                .filter(row -> row.inputs().stream().map(FixtureTemplate::text)
                        .anyMatch(text -> text.contains("below = [Node")))
                .toList());
        String human = humanOf(compilation);
        // Said as what was tried and refused, and never as a point no value can stand at.
        assertTrue(human.contains("every value tried"), human);
        assertFalse(human.contains("no row can stand at the IN point"), human);
    }

    /**
     * A border far past what a row is worth writing is a figure of this compiler's that was
     * reached, and not a tree built of that many nodes: the point is left undecided under the
     * figure and is not said to be a point no value can stand at.
     */
    @Test
    void aBorderFarPastWhatARowIsWorthWritingStopsAtTheFigure() {
        Compilation compilation = measuredModel(
                DEEPEST_LINE_MODEL.formatted(SEARCH, "").replace(">= 2", ">= 100000")
                        .replace("| \"a\" : (tree, 2) -> Yes", "| \"a\" : (tree, 2) -> No"));
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList());
        String human = humanOf(compilation);
        assertTrue(human.contains("how many elements a proposed collection holds"), human);
        assertFalse(human.contains("no row can stand at the"), human);
    }

    private static final String ONE_VALUE_MODEL = """
            module demo

            data Tag = Int
                invariant value == 1
            data Node = { v: Tag, below: List<Node> }
            data Yes
            data No

            let pathTo (node: Node, w: Tag): List<Tag> =
                if node.v == w
                    then [ node.v ]
                    else {
                        let below = List.fold((found, r) ->
                                if List.isEmpty(found) then pathTo(r, w) else found,
                            [], node.below)
                        if List.isEmpty(below) then [] else [ node.v ] ++ below
                    }

            behavior f : (root: Node, w: Tag) -> Yes | No
            let f (root, w) =
                if List.length(pathTo(root, w)) >= 2 then Yes else No

            %s""";

    /**
     * A field that has one value can hold the value searched for and no other: a row at the line
     * of one node is offered and meets its point, and the points past it and below it are said to
     * lack another value to write, which is no reason to offer nothing.
     *
     * <p>This is the report's side of it. The row at the line of one is also what the trees
     * composed from the type alone come to when every node holds the one value, so the report
     * would show it even if the chain were refused; what the chain is asked for is in
     * {@code TermRealizations#aLineToTheValue}, which asks for another value only where the line
     * is not of one.
     */
    @Test
    void aFieldThatHasOneValueIsOfferedARowAtTheLineOfOne() {
        // With no row at the line of one, so that it is owed.
        Compilation before = measuredModel(ONE_VALUE_MODEL.formatted(""));
        assertEquals(List.of(), before.errors().stream()
                .map(each -> each.diagnostic().code()).toList());
        List<String> offered = Adequacy.offeredFor(before.db(),
                        OfferingRequest.overTheModule("demo"))
                .rowsByBehavior().getOrDefault("f", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
        assertFalse(offered.isEmpty(), () -> "a row for the line of one: " + humanOf(before));
        StringBuilder written = new StringBuilder("example f\n");
        int named = 0;
        for (String inputs : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (").append(inputs)
                    .append(") -> No\n");
        }
        Compilation after = measuredModel(ONE_VALUE_MODEL.formatted(written));
        assertEquals(List.of(), after.errors().stream()
                .map(each -> each.diagnostic().code()).toList());
        String human = humanOf(after);
        assertTrue(human.contains("borders 1   obligations 1/4"), human);
        // And what no node can be written for is said as what it is.
        assertTrue(human.contains("no other value than the one searched for"), human);
    }

    private static Compilation measuredModel(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String humanOf(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** A behavior that answers a case holding the line, and a behavior that asks how long it is. */
    private static final String BEHAVIOR_OF_A_LINE = """
            module demo

            data Node = { v: Int, below: List<Node> }
            data Found = { steps: List<Int> }
            data Missing = { w: Int }
            data A
            data B
            data C

            %s

            behavior g : (root: Node, w: Int) -> Found | Missing
                constructs Found, Missing
            let g (root, w) = {
                let steps = pathTo(root, w)
                guard Bool.not(List.isEmpty(steps)) else Missing { w = w }
                %s
            }

            behavior h : (root: Node, w: Int) -> A | B | C
            let h (root, w) =
                match g(root, w) with
                    | Missing -> A
                    | Found as line -> if List.length(line.steps) >= 2 then B else C
            """;

    private static String humanReportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList());
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** The number is what the case a behavior answers holds in one field, wherever the behavior
     *  that asks about it is. */
    @Test
    void whatTheCaseABehaviorAnswersHoldsIsReadThroughTheBodyThatBuiltIt() {
        String human = humanReportOf(BEHAVIOR_OF_A_LINE.formatted(SEARCH,
                "Found { steps = steps }"));
        String ofH = human.substring(human.indexOf("  h "));
        assertFalse(ofH.contains("not read"), human);
        assertTrue(ofH.contains("borders 1"), human);
    }

    /** Built in two places, the case holds a different number in each, and that is no number of
     *  the call. */
    @Test
    void aCaseABehaviorBuildsInMoreThanOnePlaceIsNotReadThroughItsBody() {
        String human = humanReportOf(BEHAVIOR_OF_A_LINE.formatted(SEARCH, """
                if List.length(steps) > 5 then Found { steps = [] } else Found { steps = steps }"""));
        String ofH = human.substring(human.indexOf("  h "));
        assertTrue(ofH.contains("not read"), human);
    }

    @Test
    void theApprovalChainOfARoleIsReadAsTheLengthOfTheLineToTheSubmitter() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data UserId = String
                    invariant String.length(value) >= 1
                data RoleName = String
                    invariant String.length(value) >= 1
                data RoleNode =
                    { role: RoleName
                    , holder: UserId
                    , reports: List<RoleNode>
                    }
                data ReportingChain = { steps: List<UserId> }
                data NotInHierarchy = { user: UserId }

                let pathTo (node: RoleNode, user: UserId): List<UserId> =
                    if node.holder == user
                        then [ node.holder ]
                        else {
                            let below = List.fold((found, r) ->
                                    if List.isEmpty(found) then pathTo(r, user) else found,
                                [], node.reports)
                            if List.isEmpty(below) then [] else [ node.holder ] ++ below
                        }

                behavior chainTo : (root: RoleNode, user: UserId) -> ReportingChain | NotInHierarchy
                    constructs ReportingChain, NotInHierarchy
                let chainTo (root, user) = {
                    let steps = pathTo(root, user)
                    guard Bool.not(List.isEmpty(steps)) else NotInHierarchy { user = user }
                    ReportingChain { steps = steps }
                }

                data SalesManager
                data RegionalVp
                data Cfo
                data ApproverRole = SalesManager | RegionalVp | Cfo
                data ApprovalChain = { role: ApproverRole, approvers: List<UserId> }
                data SubmitterNotInHierarchy = { submitter: UserId }
                data NoAuthorityAbove = { submitter: UserId, needed: Int, available: Int }

                let levelsFor (role: ApproverRole): Int =
                    match role with
                        | SalesManager -> 1
                        | RegionalVp   -> 2
                        | Cfo          -> 3

                behavior approvalChainFor : (root: RoleNode, submitter: UserId, role: ApproverRole)
                        -> ApprovalChain | SubmitterNotInHierarchy | NoAuthorityAbove
                    constructs ApprovalChain, SubmitterNotInHierarchy, NoAuthorityAbove

                let approvalChainFor (root, submitter, role) =
                    match chainTo(root, submitter) with
                        | NotInHierarchy -> SubmitterNotInHierarchy { submitter = submitter }
                        | ReportingChain as line -> {
                            let above = List.drop(1, List.reverse(line.steps))
                            let needed = levelsFor(role)
                            guard List.length(above) >= needed
                                else NoAuthorityAbove { submitter = submitter, needed = needed
                                                      , available = List.length(above) }
                            ApprovalChain { role = role, approvers = List.take(needed, above) }
                        }

                let acmeOrg = RoleNode { role = RoleName("CEO"), holder = UserId("u-ceo"), reports =
                    [ RoleNode { role = RoleName("VP"), holder = UserId("u-vp"), reports =
                        [ RoleNode { role = RoleName("Mgr"), holder = UserId("u-mgr"), reports =
                            [ RoleNode { role = RoleName("Rep"), holder = UserId("u-rep"), reports = [] } ] } ] } ] }

                example approvalChainFor
                    | "one above" : (acmeOrg, UserId("u-mgr"), SalesManager)
                        -> ApprovalChain { role = SalesManager, approvers = [ UserId("u-vp") ] }
                    | "ghost" : (acmeOrg, UserId("u-ghost"), SalesManager)
                        -> SubmitterNotInHierarchy { submitter = UserId("u-ghost") }
                    | "ceo" : (acmeOrg, UserId("u-ceo"), SalesManager)
                        -> NoAuthorityAbove { submitter = UserId("u-ceo"), needed = 1, available = 0 }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList());
        AdequacyReport report = AdequacyReport.of(compilation);
        String json = report.json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        String human = report.human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        assertFalse(json.contains("rule_about_a_derived_value"), human);
        assertTrue(json.contains("searched_line"), human);
        String ofTheChain = human.substring(human.indexOf("  approvalChainFor "));
        assertFalse(ofTheChain.contains("not read"), human);
        assertTrue(ofTheChain.contains("borders 3"), human);
        // Rows are offered for the points of every role's border, down to a line of five nodes
        // for the role that needs three above the submitter, each holding the submitter only at
        // its last node.
        List<String> offered = Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("demo"))
                .rowsByBehavior().getOrDefault("approvalChainFor", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
        assertTrue(offered.stream().anyMatch(row ->
                        row.split("reports = \\[RoleNode", -1).length >= 5
                                && row.endsWith("Cfo")),
                () -> "offered " + offered);
    }

    // The proposition and its helpers.

    /** Each line {@code stated} counts, at the weight it has. */
    private static Map<RunSource, ExactRatio> linesIn(Proposition stated) {
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, stated);
        Relation.Affine affine = assertInstanceOf(Relation.Affine.class, compared.relation());
        Map<RunSource, ExactRatio> out = new LinkedHashMap<>();
        List<Quantity> others = new ArrayList<>();
        affine.form().coefs().forEach((number, by) -> {
            if (number instanceof DecisionAtom.OfTheInput(NumericTerm.TakenOver over)
                    && over.source() instanceof RunSource.SearchedLine) {
                assertInstanceOf(TakenAs.HowManyItHolds.class, over.takenAs());
                out.put(over.source(), by);
            } else {
                others.add(number);
            }
        });
        assertEquals(1, others.size(), () -> "a number of the input beside the line: " + others);
        return out;
    }

    private static void assertUnread(Proposition stated) {
        assertTrue(Proposition.leavesSomethingUnread(stated), () -> "read as " + stated);
    }

    /** What the condition of {@code f}'s one fork states, with {@code lets} declared beside it. */
    private static Proposition stated(String lets, String condition) {
        Compilation compilation = Compilation.ofSource(DECLARATIONS + lets + """

                behavior f : (i: In) -> Int
                let f (i) =
                    if (%s) then 1 else 0
                """.formatted(condition), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), () -> "compiles: " + condition);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReading read = inputs.reading(rules);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core.If fork = assertInstanceOf(Core.If.class, Core.withoutStanding(analysis.core()));
        return Pullback.ofATruth(fork.cond(), reads, read, Optional.empty()).proposition();
    }
}
