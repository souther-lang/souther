package souther.compiler.cst;

import org.junit.jupiter.api.Test;

import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which node kinds are expressions, which tokens can be a binary operator, and which direct
 * children of a node they select are facts about the tree. The formatter and the AST builder both
 * ask the tree rather than keeping a list of their own.
 *
 * <p>The two sets are held here against a spelling written out by hand, because the classification
 * has a default arm and a kind added to the grammar is not refused by the compiler until it is
 * placed.
 */
class TheTreeSaysWhichChildrenAreExpressionsTest {

    private static SyntaxNode firstOf(SyntaxNode node, SyntaxKind kind) {
        if (node.kind() == kind) {
            return node;
        }
        for (SyntaxNode child : node.childNodes()) {
            SyntaxNode found = firstOf(child, kind);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    private static SyntaxNode find(String body, SyntaxKind kind) {
        SyntaxNode root = CstParser.parse("module demo\nlet f (x) = " + body + "\n").root();
        SyntaxNode found = firstOf(root, kind);
        assertTrue(found != null, kind + " in " + body);
        return found;
    }

    private static List<String> texts(List<SyntaxNode> nodes) {
        return nodes.stream().map(node -> node.text().strip()).toList();
    }

    @Test
    void exactlyTheseKindsAreExpressions() {
        Set<SyntaxKind> expressions = EnumSet.of(
                SyntaxKind.LITERAL_EXPR, SyntaxKind.VAR_EXPR, SyntaxKind.FIELD_ACCESS,
                SyntaxKind.APPLY_EXPR, SyntaxKind.BINARY_EXPR, SyntaxKind.UNARY_EXPR,
                SyntaxKind.PIPE_EXPR, SyntaxKind.PAREN_EXPR, SyntaxKind.TUPLE_EXPR,
                SyntaxKind.LIST_EXPR, SyntaxKind.LIST_COMP, SyntaxKind.IF_EXPR,
                SyntaxKind.MATCH_EXPR, SyntaxKind.LAMBDA_EXPR, SyntaxKind.FIELD_GETTER,
                SyntaxKind.NEW_DATA_EXPR, SyntaxKind.BLOCK_EXPR, SyntaxKind.UNREACHABLE_EXPR);
        Set<SyntaxKind> said = EnumSet.allOf(SyntaxKind.class).stream()
                .filter(SyntaxKind::isExpression)
                .collect(Collectors.toCollection(() -> EnumSet.noneOf(SyntaxKind.class)));
        assertEquals(expressions, said);
    }

    @Test
    void exactlyTheseKindsCanBeABinaryOperator() {
        Set<SyntaxKind> operators = EnumSet.of(
                SyntaxKind.EQ, SyntaxKind.NE, SyntaxKind.LT, SyntaxKind.LE, SyntaxKind.GT,
                SyntaxKind.GE, SyntaxKind.AND, SyntaxKind.OR, SyntaxKind.PLUS, SyntaxKind.MINUS,
                SyntaxKind.STAR, SyntaxKind.SLASH, SyntaxKind.PLUSPLUS);
        Set<SyntaxKind> said = EnumSet.allOf(SyntaxKind.class).stream()
                .filter(SyntaxKind::isBinaryOperator)
                .collect(Collectors.toCollection(() -> EnumSet.noneOf(SyntaxKind.class)));
        assertEquals(operators, said);
    }

    @Test
    void aBinaryExpressionHasItsTwoOperandsInSourceOrder() {
        SyntaxNode binary = find("a + b", SyntaxKind.BINARY_EXPR);
        assertEquals(List.of("a", "b"), texts(binary.expressionChildren()));
        assertEquals("a", binary.firstExpressionChild().text().strip());
        assertEquals("b", binary.lastExpressionChild().text().strip());
        assertEquals(SyntaxKind.PLUS, binary.binaryOperatorToken().kind());
    }

    @Test
    void anApplicationIsNotEnteredPastItsArgumentList() {
        SyntaxNode apply = find("g(a + b, c)", SyntaxKind.APPLY_EXPR);
        assertEquals(List.of("g"), texts(apply.expressionChildren()));
        SyntaxNode args = apply.child(SyntaxKind.ARG_LIST).orElseThrow();
        assertEquals(List.of("a + b", "c"), texts(args.expressionChildren()));
    }

    @Test
    void childNodesOfAKindAreTheDirectOnesOnly() {
        SyntaxNode apply = find("g(a + b, c)", SyntaxKind.APPLY_EXPR);
        assertEquals(1, apply.childNodes(SyntaxKind.ARG_LIST).size());
        assertEquals(List.of(), apply.childNodes(SyntaxKind.BINARY_EXPR));
    }

    @Test
    void aNodeWithNoExpressionAnswersEmptyAndTheRequiredFormsThrow() {
        SyntaxNode args = find("g()", SyntaxKind.ARG_LIST);
        assertEquals(List.of(), args.expressionChildren());
        assertTrue(args.firstExpressionChildOpt().isEmpty());
        assertThrows(IndexOutOfBoundsException.class, args::firstExpressionChild);
        assertThrows(IndexOutOfBoundsException.class, args::lastExpressionChild);
    }

    @Test
    void aFieldWithoutAValueHasNoExpressionAndOneWithAValueHasIt() {
        SyntaxNode shorthand = find("T { a }", SyntaxKind.FIELD_INIT);
        assertTrue(shorthand.firstExpressionChildOpt().isEmpty());
        SyntaxNode written = find("T { a = b }", SyntaxKind.FIELD_INIT);
        assertEquals("b", written.firstExpressionChildOpt().orElseThrow().text().strip());
    }

    @Test
    void aNodeWithoutAnOperatorTokenSaysSo() {
        SyntaxNode paren = find("(a)", SyntaxKind.PAREN_EXPR);
        assertThrows(IllegalStateException.class, paren::binaryOperatorToken);
    }
}
