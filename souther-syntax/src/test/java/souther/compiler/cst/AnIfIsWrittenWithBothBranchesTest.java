package souther.compiler.cst;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An {@code if} carries both of its branches, which is what makes the question of where an
 * {@code else} belongs answerable by counting.
 *
 * <p>The specification states the association, and an association is not a set the compiler
 * enumerates anywhere — no list of tokens or kinds says which {@code then} an {@code else} closes.
 * So it is held here, against the parser that decides it, by reading the tree the two forms build.
 */
class AnIfIsWrittenWithBothBranchesTest {

    private static SyntaxNode outermostIf(SyntaxNode node) {
        if (node.kind() == SyntaxKind.IF_EXPR) {
            return node;
        }
        for (SyntaxNode child : node.childNodes()) {
            SyntaxNode found = outermostIf(child);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    private static List<String> branchesOf(String src) {
        return outermostIf(CstParser.parse(src).root()).childNodes().stream()
                .map(node -> node.text().strip())
                .toList();
    }

    @Test
    void theElseClosesTheNearestThenThatIsStillOpen() {
        assertEquals(List.of("a", "if b then c else d", "e"), branchesOf("""
                module demo
                let f (x) = if a then if b then c else d else e
                """));
    }

    @Test
    void anIfWithoutItsElseDoesNotRead() {
        List<String> said = CstParser.parse("""
                module demo
                let f (x) = if a then b
                """).errors().stream()
                .map(error -> error.said().getClass().getSimpleName())
                .toList();
        assertEquals("AnExpressionExpectedSomethingElse", said.getFirst());
    }
}
