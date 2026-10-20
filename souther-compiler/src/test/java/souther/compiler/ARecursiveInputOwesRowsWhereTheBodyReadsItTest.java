package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
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
 * A row is owed at a position of a recursive input where the body reads it, and nowhere else.
 *
 * <p>The listing of positions ends where the input returns to a declaration the path has opened,
 * so what a type states about the value that comes back is not listed again. That leaves nothing
 * owed that was owed before: what a position is owed rows for is what the body states about it,
 * and a path the body names is read past the return. The same holds with no recursion, where the
 * type's declared classes at a position the body never reads are said and owe no row.
 */
class ARecursiveInputOwesRowsWhereTheBodyReadsItTest {

    private static final String NODE = """
            module m
            data Yes
            data No
            data Node = { amount: Int, kids: List<Node> }
                invariant amount /= 0
            """;

    @Test
    void aBodyThatReadsOnlyTheNodeOwesNothingAtTheNodesBelow() {
        String report = humanReportOf(NODE + """
                behavior f : (n: Node) -> Yes | No
                let f (n) = if n.amount > 3 then Yes else No
                """);

        assertTrue(report.contains("read as f/n.amount"), report);
        assertFalse(report.contains("n.kids[*].amount: ="), report);
    }

    @Test
    void aBodyThatReadsWhatTheNodesBelowHoldOwesRowsThere() {
        String report = humanReportOf(NODE + """
                behavior f : (n: Node) -> Yes | No
                let f (n) = if List.any(k -> k.amount > 3, n.kids) then Yes else No
                """);

        assertTrue(report.contains("read as f/n.kids[*].amount: = 3"), report);
        assertTrue(report.contains("border      borders 1   obligations 0/4"), report);
    }

    @Test
    void aTypeThatDoesNotRecurseSaysTheSameOfAPositionTheBodyNeverReads() {
        String report = humanReportOf("""
                module m
                data Yes
                data No
                data Item = { amount: Int }
                    invariant amount /= 0
                data Node = { amount: Int, kids: List<Item> }
                    invariant amount /= 0
                behavior f : (n: Node) -> Yes | No
                let f (n) = if n.amount > 3 then Yes else No
                """);

        assertTrue(report.contains("about `n.kids[*].amount`"), report);
        assertFalse(report.contains("n.kids[*].amount: ="), report);
    }

    /**
     * A rule of the type about a place under the return is owed rows there, as it is where the type
     * does not recurse.
     *
     * <p>The rule of a link says something of `next.limit`, the chain it holds, which is the
     * position the listing ends at. The place it names stands under each case of that chain, and
     * the line is drawn there: a line at a number, and a line between two places, whose second
     * place a reader that went only where an end was put would never reach.
     *
     * <p>Held on the places the declaration's obligations are read at, which is what a row is
     * written toward, and on there being nothing further down than the rule names. A conjunct that
     * holds a second statement about other fields is held to the same: that statement is owed
     * where the link itself stands, and the copy of the link under the return, which nothing
     * listed, owes neither of them.
     */
    @Test
    void aRuleAboutAPlaceUnderTheReturnIsOwedRowsThereAsWhereTheTypeDoesNotRecurse() {
        for (String rule : List.of("next.limit >= 0", "next.limit <= limit",
                "next.limit <= limit && x <= y")) {
            List<String> recursive = declaredReadingsOf(PAGED + """
                    data Link = { ...Paging, x: Int, y: Int, next: Chain }
                        invariant %s
                    data Chain = Leaf | Link
                    """.formatted(rule) + PAGED_BEHAVIOR);
            List<String> flat = declaredReadingsOf(PAGED + """
                    data Other = { ...Paging, tag: Bool }
                    data Inner = Leaf | Other
                    data Link = { ...Paging, x: Int, y: Int, next: Inner }
                        invariant %s
                    data Chain = Leaf | Link
                    """.formatted(rule) + PAGED_BEHAVIOR);

            assertEquals(flat.stream().map(each -> each.replace("@Other.", "@Link.")).sorted()
                            .toList(),
                    recursive.stream().sorted().toList(),
                    rule + ": the same readings, each as many times as where the type does not "
                            + "recurse");
            assertTrue(recursive.contains("f/c@Link.next@Leaf.limit"), rule);
            assertTrue(recursive.contains("f/c@Link.next@Link.limit"), rule);
        }
    }

    private static final String PAGED = """
            module m
            data Yes
            data No
            data Paging = { limit: Int }
            data Leaf = { ...Paging, terminal: Bool }
            """;

    private static final String PAGED_BEHAVIOR = """
            behavior f : (c: Chain) -> Yes | No
            let f (c) = if c.limit > 3 then Yes else No
            """;

    /**
     * The axes the obligations of the declarations are read at, in the report's own words, once for
     * each reading: an obligation counted twice is two entries here.
     */
    private static List<String> declaredReadingsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(0, compilation.errors().size(), "the model compiles");
        JsonNode module = JsonMapper.builder().build()
                .readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0);
        List<String> axes = new ArrayList<>();
        for (JsonNode declaration : module.get("declarations")) {
            for (JsonNode obligation : declaration.get("obligations")) {
                for (JsonNode reading : obligation.get("readings")) {
                    axes.add(reading.get("axis").asString());
                }
            }
        }
        return axes;
    }

    private static String humanReportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(0, compilation.errors().size(), "the model compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
