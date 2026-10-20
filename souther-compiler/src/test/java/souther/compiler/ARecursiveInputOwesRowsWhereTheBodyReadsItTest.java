package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

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
     * A line a rule of the type draws at a place under the return is owed rows there, as it is
     * where the type does not recurse.
     *
     * <p>The rule of a link says `next.limit >= 0` of the chain it holds, which is the position the
     * listing ends at. The place it names stands under each case of that chain, and the line is
     * drawn there.
     */
    @Test
    void aLineARuleDrawsUnderTheReturnIsOwedRowsThereAsWhereTheTypeDoesNotRecurse() {
        String recursive = humanReportOf(PAGED + """
                data Link = { ...Paging, next: Chain }
                    invariant next.limit >= 0
                data Chain = Leaf | Link
                """ + PAGED_BEHAVIOR);
        String flat = humanReportOf(PAGED + """
                data Other = { ...Paging, tag: Bool }
                data Inner = Leaf | Other
                data Link = { ...Paging, next: Inner }
                    invariant next.limit >= 0
                data Chain = Leaf | Link
                """ + PAGED_BEHAVIOR);

        for (String report : java.util.List.of(recursive, flat)) {
            assertTrue(report.contains("declarations   borders 1   obligations 0/2"), report);
            assertTrue(report.contains("read as f/c@Link.next@Leaf.limit: = 0"), report);
        }
        assertTrue(recursive.contains("read as f/c@Link.next@Link.limit: = 0"), recursive);
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

    private static String humanReportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(0, compilation.errors().size(), "the model compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
