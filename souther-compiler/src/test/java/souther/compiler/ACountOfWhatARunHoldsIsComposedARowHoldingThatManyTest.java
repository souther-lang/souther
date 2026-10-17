package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A decision rule whose condition compares how many values a run holds — every element of the
 * lists inside a list, or every node a tree holds from its root down — is composed a row holding
 * that many, the way a total of a run is.
 *
 * <p>Held by running the rows. Each row composed for a rule is put back as an example, answered
 * with what the condition works out to over the row, counted here apart from anything the compiler
 * read: the nodes of a tree at every depth the row writes, and the elements of every list inside
 * every element. A row standing short of its rule, or a count read wrong, is an example the model
 * answers otherwise.
 *
 * <p>And a tree is written as a root and nodes below it holding nothing below them. A count of nodes
 * such a tree cannot hold — the rules hold each node to one below it — is a tree this writes none
 * of, and is never said to be a count no tree comes to.
 */
class ACountOfWhatARunHoldsIsComposedARowHoldingThatManyTest {

    /** Every node of a tree, one value for each. */
    private static final String THE_NODES = """
            module p
            data Node = { holder: Int, reports: List<Node> }
            let everyone (node: Node): List<Int> =
                [ node.holder ] ++ List.flatMap(r -> everyone(r), node.reports)
            behavior pick : (root: Node) -> Int
            let pick (root) = if List.length(everyone(root)) >= 3 then 1 else 0
            """;

    /** The same against a number a row writes. */
    private static final String THE_NODES_AGAINST_AN_INPUT = """
            module p
            data Node = { holder: Int, reports: List<Node> }
            let everyone (node: Node): List<Int> =
                [ node.holder ] ++ List.flatMap(r -> everyone(r), node.reports)
            behavior pick : (root: Node, needed: Int) -> Int
            let pick (root, needed) = if List.length(everyone(root)) >= needed then 1 else 0
            """;

    /** Every element of the lists inside a list, and one more. */
    private static final String THE_LISTS_OF_A_LIST = """
            module p
            data Team = { holder: Int, items: List<Int> }
            data Org = { head: Int, teams: List<Team> }
            behavior pick : (org: Org, needed: Int) -> Int
            let pick (org, needed) =
                if List.length([ org.head ] ++ List.flatMap(t -> t.items, org.teams)) >= needed
                then 1 else 0
            """;

    /** How many elements a list holds, counted by a walk adding one for each. */
    private static final String A_WALK_COUNTING = """
            module p
            behavior pick : (xs: List<Int>) -> Int
            let pick (xs) = if List.fold((acc, x) -> acc + 1, 0, xs) == 1 then 1 else 0
            """;

    /** Each model, with what its condition works out to over a row's inputs. */
    private static final Map<String, Function<List<Hir.Expr>, Integer>> ANSWERED = Map.of(
            THE_NODES, row -> nodesOf(row.get(0)) >= 3 ? 1 : 0,
            THE_NODES_AGAINST_AN_INPUT, row -> nodesOf(row.get(0)) >= wholeNumber(row.get(1))
                    ? 1 : 0,
            THE_LISTS_OF_A_LIST, row -> 1 + elementsOf(row.get(0), "items")
                    >= wholeNumber(row.get(1)) ? 1 : 0,
            A_WALK_COUNTING, row -> elementsOf(row.get(0)) == 1 ? 1 : 0);

    @Test
    void everyRuleIsComposedARowThatTakesIt() {
        ANSWERED.forEach((model, answered) -> {
            List<String> examples = new ArrayList<>();
            Set<Integer> answers = new TreeSet<>();
            for (List<FixtureTemplate> row : composedForTheRules(measured(model))) {
                int answer = answered.apply(row.stream().map(FixtureTemplate::value).toList());
                answers.add(answer);
                examples.add("    | \"composed " + examples.size() + "\" : ("
                        + String.join(", ", row.stream().map(FixtureTemplate::text).toList())
                        + ") -> " + answer);
            }
            assertEquals(Set.of(0, 1), answers,
                    () -> "a row for each rule: " + examples + "\n" + report(measured(model)));

            Compilation answeredBy = measured(model + "example pick\n"
                    + String.join("\n", examples) + "\n");
            assertEquals(List.of(), answeredBy.errors().stream()
                    .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                    .toList(), () -> "each row is answered as its inputs say: " + examples);
        });
    }

    /**
     * A tree whose nodes each hold one below them at the most: three nodes are a chain, deeper than
     * a root and the nodes below it. The row is one this writes none of, and the rule is not one
     * no row takes.
     */
    @Test
    void aCountOfNodesNoTreeThisWritesHoldsIsNoCountNoTreeComesTo() {
        String report = report(measured("""
                module p
                data Node = { holder: Int, reports: List<Node> }
                    invariant List.length(reports) <= 1
                let everyone (node: Node): List<Int> =
                    [ node.holder ] ++ List.flatMap(r -> everyone(r), node.reports)
                behavior pick : (root: Node) -> Int
                let pick (root) = if List.length(everyone(root)) >= 3 then 1 else 0
                """));
        List<String> atTheLine = report.lines().filter(line -> line.contains("ON point")).toList();
        assertFalse(atTheLine.isEmpty(), () -> report);
        assertTrue(atTheLine.stream().noneMatch(line -> line.contains("no row can stand")),
                () -> "a chain of three is a tree, written or not: " + report);
    }

    /**
     * And a tree holds its root, so a count of none is one no tree comes to: at two nodes or more
     * the point below the line is none, and no row stands there.
     */
    @Test
    void noTreeHoldsNoNodes() {
        String report = report(measured(THE_NODES.replace(">= 3", ">= 2")));
        assertTrue(report.lines().anyMatch(line -> line.contains("no row can stand at the OUT"
                + " point")), () -> report);
    }

    /** The rows composed for the decision rules no row takes, each as its inputs. */
    private static List<List<FixtureTemplate>> composedForTheRules(Compilation compilation) {
        List<List<FixtureTemplate>> out = new ArrayList<>();
        Adequacy.generatedOf(compilation.db(), compilation.modules().get(0)).get("pick")
                .generation().stream()
                .filter(each -> each.finding().about() instanceof About.ARuleNoRowTakes)
                .forEach(each -> {
                    if (each.outcome() instanceof GenerationOutcome.Generated made) {
                        made.candidates().forEach(row -> out.add(row.inputs()));
                    }
                });
        return out;
    }

    /** How many nodes the tree {@code value} writes holds, at every depth. */
    private static long nodesOf(Hir.Expr value) {
        return switch (value) {
            case Hir.Apply applied when applied.args().size() == 1 ->
                    nodesOf(applied.args().getFirst());
            case Hir.NewData node -> 1 + node.inits().stream()
                    .filter(each -> each.name().equals("reports"))
                    .mapToLong(each -> ((Hir.ListLit) each.value()).elements().stream()
                            .mapToLong(ACountOfWhatARunHoldsIsComposedARowHoldingThatManyTest
                                    ::nodesOf).sum())
                    .sum();
            default -> throw new AssertionError("a node: " + value);
        };
    }

    /** How many elements the lists at {@code field} hold, wherever in {@code value} a record holds
     *  one. */
    private static long elementsOf(Hir.Expr value, String field) {
        return switch (value) {
            case Hir.Apply applied -> applied.args().stream()
                    .mapToLong(each -> elementsOf(each, field)).sum();
            case Hir.ListLit list -> list.elements().stream()
                    .mapToLong(each -> elementsOf(each, field)).sum();
            case Hir.NewData record -> record.inits().stream()
                    .mapToLong(each -> each.name().equals(field)
                            ? elementsOf(each.value()) : elementsOf(each.value(), field))
                    .sum();
            default -> 0;
        };
    }

    /** How many elements the list {@code value} writes holds. */
    private static long elementsOf(Hir.Expr value) {
        return switch (value) {
            case Hir.Apply applied when applied.args().size() == 1 ->
                    elementsOf(applied.args().getFirst());
            case Hir.ListLit list -> list.elements().size();
            default -> throw new AssertionError("a list: " + value);
        };
    }

    /** The whole number {@code value} writes. */
    private static long wholeNumber(Hir.Expr value) {
        return switch (value) {
            case Hir.IntLit number -> number.value();
            case Hir.Neg negated -> -wholeNumber(negated.operand());
            default -> throw new AssertionError("a whole number: " + value);
        };
    }

    /** Each model measured once for the class: the methods read the same models, and only read
     *  them. */
    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static Compilation measured(String source) {
        return MEASURED.computeIfAbsent(source, text -> {
            Compilation compilation = Compilation.ofSource(text, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            return compilation;
        });
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
