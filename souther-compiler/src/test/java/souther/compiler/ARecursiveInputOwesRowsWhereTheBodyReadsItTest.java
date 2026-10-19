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

    private static String humanReportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(0, compilation.errors().size(), "the model compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
