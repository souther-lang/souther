package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PlacesMoved;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.semantics.TakenAs;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many a helper searching down a tree answers is read as a number of the nodes it reaches: how
 * many there are, or how many a container of each node holds over all of them, at the weight each
 * node adds — where the body says that of every node, by induction. Where the body adds what the
 * nodes below answer twice, of some of them, or calls itself on no node below, the number is not
 * read, and nothing is made up for it.
 */
class HowManyASearchAnswersIsCountedOverTheNodesItReachesTest {

    private static final String DECLARATIONS = """
            module demo

            data Node = { v: Int, items: List<Int>, below: List<Node> }
            data Item = { tags: List<Int> }
            data Order = { items: List<Item> }
            data In = { t: Node, w: Int, ts: List<Node>, orders: List<Order> }
            """;

    private static final TermPath T = TermPath.of("i").then("t");

    private static final String EVERYONE = """
            let everyone (node: Node): List<Int> =
                [ node.v ] ++ List.flatMap(r -> everyone(r), node.below)
            """;

    @Test
    void oneValueForEachNodeIsHowManyNodesThereAre() {
        assertEquals(Map.of(nodes(List.of()), ExactRatio.ONE),
                countsIn(stated(EVERYONE, "List.length(everyone(i.t)) >= 2")));
    }

    @Test
    void twoValuesForEachNodeAreTwiceHowManyNodesThereAre() {
        assertEquals(Map.of(nodes(List.of()), ExactRatio.of(2)), countsIn(stated("""
                let both (node: Node): List<Int> =
                    [ node.v, node.v ] ++ List.flatMap(r -> both(r), node.below)
                """, "List.length(both(i.t)) >= 3")));
    }

    @Test
    void whatEachNodeHoldsInAContainerIsHowManyItHoldsOverEveryNode() {
        assertEquals(Map.of(nodes(List.of("items")), ExactRatio.ONE), countsIn(stated("""
                let items (node: Node): List<Int> =
                    node.items ++ List.flatMap(r -> items(r), node.below)
                """, "List.length(items(i.t)) >= 3")));
    }

    /** A number of the input is held against one too, which no count of the nodes settles. */
    @Test
    void aCountHeldAgainstAnInputIsTheSameCount() {
        Map<RunSource, ExactRatio> counted =
                countsIn(stated(EVERYONE, "List.length(everyone(i.t)) >= i.w"));
        assertEquals(Map.of(nodes(List.of()), ExactRatio.ONE), counted);
    }

    @Test
    void whatTheNodesBelowAnswerAddedTwiceIsNotACountOfTheNodes() {
        assertUnread(stated("""
                let twice (node: Node): List<Int> =
                    [ node.v ] ++ List.flatMap(r -> twice(r) ++ twice(r), node.below)
                """, "List.length(twice(i.t)) >= 3"));
    }

    @Test
    void whatSomeOfTheNodesBelowAnswerIsNotACountOfTheNodes() {
        assertUnread(stated("""
                partial let kept (node: Node): List<Int> =
                    [ node.v ] ++ List.flatMap(r -> kept(r),
                        List.filter(r -> r.v > 0, node.below))
                """, "List.length(kept(i.t)) >= 2"));
    }

    @Test
    void aCallOnTheSameNodeIsNoCount() {
        assertUnread(stated("""
                partial let stuck (node: Node): List<Int> =
                    [ node.v ] ++ List.flatMap(r -> stuck(node), node.below)
                """, "List.length(stuck(i.t)) >= 2"));
    }

    /** What a node adds of a value that stays put under the top node is not the node's own. */
    @Test
    void aValueThatStaysPutUnderTheNodeIsNoCount() {
        assertUnread(stated("""
                let along (node: Node, top: List<Int>): List<Int> =
                    top ++ List.flatMap(r -> along(r, top), node.below)
                """, "List.length(along(i.t, i.t.items)) >= 2"));
    }

    /**
     * A tree, or a container, one of many read under a statement about each of them is not every
     * occurrence of its path: the nodes of one tree of a list, and the tags of one order's items,
     * are no count of a run over all of them.
     */
    @Test
    void oneOfManyIsNoRunOverAllOfThem() {
        assertNoRunOverAllOfThem(stated(EVERYONE,
                "List.all(t -> List.length(everyone(t)) >= 2, i.ts)"));
        for (String counted : List.of(
                "List.sum(List.map(e -> List.length(e.tags), o.items))",
                "List.length(List.flatMap(e -> e.tags, o.items))")) {
            assertNoRunOverAllOfThem(stated("", "List.all(o -> " + counted + " <= 5, i.orders)"));
        }
    }

    /**
     * And a run of the nodes below one root is that run wherever the root is moved to, but none
     * where it is moved inside a container: the nodes below every element's tree are no one
     * tree's, which no such run is made over however it is reached.
     */
    @Test
    void theNodesOfOneTreeMovedInsideAContainerAreNoRun() {
        RunSource.ReachableNodes nodes = nodes(List.of());
        TermPath other = TermPath.of("j").then("t");
        TermPath everyTree = TermPath.of("i").then("ts").element();
        assertEquals(new RunSource.ReachableNodes(other, List.of("below"), List.of()),
                nodes.movedTo(PlacesMoved.by(_ -> other)));
        assertNull(nodes.movedTo(PlacesMoved.by(_ -> everyTree)));
        assertThrows(IllegalArgumentException.class,
                () -> new RunSource.ReachableNodes(everyTree, List.of("below"), List.of()));
    }

    /** That {@code stated} counts no run over every node below every tree, or every tag of every
     *  order's items, whatever else it is read as. */
    private static void assertNoRunOverAllOfThem(Proposition stated) {
        assertTrue(!stated.spelledOut().contains("node below") && !stated.spelledOut().contains("tags[*])"),
                () -> "read as " + stated);
    }

    private static RunSource.ReachableNodes nodes(List<String> container) {
        return new RunSource.ReachableNodes(T, List.of("below"), container);
    }

    private static void assertUnread(Proposition stated) {
        assertTrue(Proposition.leavesSomethingUnread(stated), () -> "read as " + stated);
    }

    /**
     * Each count of a run of nodes {@code stated} compares, by its run, at the weight it has —
     * every number it compares being one of those.
     */
    private static Map<RunSource, ExactRatio> countsIn(Proposition stated) {
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, stated);
        Relation.Affine affine = assertInstanceOf(Relation.Affine.class, compared.relation());
        Map<RunSource, ExactRatio> out = new LinkedHashMap<>();
        affine.form().coefs().forEach((number, by) -> {
            if (number instanceof DecisionAtom.OfTheInput(NumericTerm.TakenOver over)
                    && over.source() instanceof RunSource.ReachableNodes) {
                assertInstanceOf(TakenAs.HowManyItHolds.class, over.takenAs());
                out.put(over.source(), by);
            } else {
                assertNoCount(number);
            }
        });
        return out;
    }

    /** A number beside the counts, which is an input's own value. */
    private static void assertNoCount(Quantity number) {
        assertEquals(new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("i")
                .then("w"))), number, "a number beside the count of the nodes");
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
