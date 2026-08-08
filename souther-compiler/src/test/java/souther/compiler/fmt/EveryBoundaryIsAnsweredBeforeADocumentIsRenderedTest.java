package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.SyntaxKind;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a {@link TokenDoc} is for: a construct hands over the tokens it writes and says of each
 * boundary whether the layout may break there, and what an unbroken boundary holds is decided
 * afterwards, in one place, from the two tokens and the construct joining them.
 *
 * <p>That the renderer never sees an unanswered boundary is not asserted here because it cannot be:
 * {@link Doc} has no boundary to render. {@link TokenDoc#resolve()} is the only way from one to the
 * other and it answers all of them, so the state does not exist rather than being checked for.
 */
class EveryBoundaryIsAnsweredBeforeADocumentIsRenderedTest {

    private static final int WIDE = 100;

    private static String render(TokenDoc doc, int width) {
        return doc.resolve().render(width);
    }

    private static TokenDoc bracketed(SyntaxKind construct) {
        return TokenDoc.node(construct, TokenDoc.concat(
                TokenDoc.token(SyntaxKind.LPAREN, "("),
                TokenDoc.GAP,
                TokenDoc.token(SyntaxKind.IDENT, "a"),
                TokenDoc.GAP,
                TokenDoc.token(SyntaxKind.RPAREN, ")")));
    }

    /**
     * The same two tokens under two constructs, written two ways. Neither document says what goes
     * between them, and the difference between the two is the construct's name and nothing else —
     * which is the whole of what the nine position-decided rows mean.
     */
    @Test
    void theSamePairIsWrittenTwoWaysUnderTwoConstructs() {
        assertEquals("( a )", render(bracketed(SyntaxKind.EXPOSING_CLAUSE), WIDE));
        assertEquals("(a)", render(bracketed(SyntaxKind.ARG_LIST), WIDE));
    }

    /** A boundary written tight is a boundary all the same: nothing in the document spells the
     * nothing between `f` and `(`. */
    @Test
    void anAdjacencyWrittenTightIsABoundaryToo() {
        TokenDoc call = TokenDoc.node(SyntaxKind.APPLY_EXPR, TokenDoc.concat(
                TokenDoc.token(SyntaxKind.IDENT, "f"),
                TokenDoc.GAP,
                TokenDoc.node(SyntaxKind.ARG_LIST, TokenDoc.concat(
                        TokenDoc.token(SyntaxKind.LPAREN, "("),
                        TokenDoc.GAP,
                        TokenDoc.token(SyntaxKind.RPAREN, ")")))));
        assertEquals("f()", render(call, WIDE));
    }

    /**
     * The construct is found from the two tokens, not from where the boundary was written. Here the
     * boundary between {@code f} and {@code (} is inside the argument list, and the answer is still
     * the application's: an argument list has no rule for a name against an opening bracket, and
     * reading the construct off the placement would have asked it for one.
     */
    @Test
    void theConstructIsTheOneJoiningTheTokensAndNotTheOneTheBoundaryWasWrittenIn() {
        TokenDoc call = TokenDoc.node(SyntaxKind.APPLY_EXPR, TokenDoc.concat(
                TokenDoc.token(SyntaxKind.IDENT, "f"),
                TokenDoc.node(SyntaxKind.ARG_LIST, TokenDoc.concat(
                        TokenDoc.GAP,
                        TokenDoc.token(SyntaxKind.LPAREN, "("),
                        TokenDoc.GAP,
                        TokenDoc.token(SyntaxKind.RPAREN, ")")))));
        assertEquals("f()", render(call, WIDE));
    }

    /**
     * Whether a boundary may break and what it holds when it does not are separate. These two
     * documents differ only in the construct, so only in what an unbroken boundary holds; broken,
     * they are the same, because the break is the layout's answer and not this rule's.
     */
    @Test
    void whetherABoundaryBreaksAndWhatItHoldsUnbrokenAreSeparate() {
        TokenDoc open = breakable(SyntaxKind.EXPOSING_CLAUSE);
        TokenDoc tight = breakable(SyntaxKind.ARG_LIST);

        assertEquals("( aaaaaaaa )", render(open, WIDE));
        assertEquals("(aaaaaaaa)", render(tight, WIDE));

        String brokenOpen = render(open, 4);
        assertEquals(brokenOpen, render(tight, 4), "broken, the two are written the same");
        assertTrue(brokenOpen.contains("\n"), "at this width both break:\n" + brokenOpen);
    }

    private static TokenDoc breakable(SyntaxKind construct) {
        return TokenDoc.node(construct, TokenDoc.group(TokenDoc.concat(
                TokenDoc.token(SyntaxKind.LPAREN, "("),
                TokenDoc.nest(4, TokenDoc.concat(
                        TokenDoc.SOFT_GAP,
                        TokenDoc.token(SyntaxKind.IDENT, "aaaaaaaa"))),
                TokenDoc.SOFT_GAP,
                TokenDoc.token(SyntaxKind.RPAREN, ")"))));
    }

    /** An adjacency no row holds is refused. A new one is a decision, and it is made in the rule
     * rather than by whichever construct writes it first. */
    @Test
    void anAdjacencyNoRowHoldsIsRefused() {
        TokenDoc unlisted = TokenDoc.node(SyntaxKind.BLOCK_EXPR, TokenDoc.concat(
                TokenDoc.token(SyntaxKind.LBRACE, "{"),
                TokenDoc.GAP,
                TokenDoc.token(SyntaxKind.LBRACE, "{")));
        IllegalStateException e =
                assertThrows(IllegalStateException.class, () -> unlisted.resolve());
        assertTrue(e.getMessage().contains("LBRACE LBRACE"), e.getMessage());
    }

    /** Two boundaries where two tokens have one adjacency. This is the shape that put two spaces
     * inside `exposing (  )`: each bracket wrote what goes just inside it, and the two met. */
    @Test
    void twoBoundariesWhereTheTokensHaveOneAdjacencyAreRefused() {
        TokenDoc doubled = TokenDoc.node(SyntaxKind.ARG_LIST, TokenDoc.concat(
                TokenDoc.token(SyntaxKind.LPAREN, "("),
                TokenDoc.SOFT_GAP,
                TokenDoc.SOFT_GAP,
                TokenDoc.token(SyntaxKind.RPAREN, ")")));
        assertThrows(IllegalStateException.class, () -> doubled.resolve());
    }

    /** A comment is not one of the two tokens a boundary joins, so a boundary standing beside one
     * has to be a boundary that always breaks — which is what a comment does to a line anyway. */
    @Test
    void aBoundaryBesideACommentHasToBreak() {
        assertThrows(IllegalStateException.class, () -> TokenDoc.node(SyntaxKind.BLOCK_EXPR,
                TokenDoc.concat(
                        TokenDoc.token(SyntaxKind.IDENT, "a"),
                        TokenDoc.SOFT_GAP,
                        TokenDoc.comment("// why"),
                        TokenDoc.HARD_GAP,
                        TokenDoc.token(SyntaxKind.IDENT, "b"))).resolve());

        String written = render(TokenDoc.node(SyntaxKind.BLOCK_EXPR, TokenDoc.concat(
                TokenDoc.token(SyntaxKind.IDENT, "a"),
                TokenDoc.HARD_GAP,
                TokenDoc.comment("// why"),
                TokenDoc.HARD_GAP,
                TokenDoc.token(SyntaxKind.IDENT, "b"))), WIDE);
        assertEquals("a\n// why\nb", written);
    }

    /** A boundary that always breaks has no unbroken form, so the rule is not asked about it — not
     * even for a pair it holds no row for. */
    @Test
    void aBoundaryThatAlwaysBreaksIsNotAsked() {
        TokenDoc unlisted = TokenDoc.node(SyntaxKind.BLOCK_EXPR, TokenDoc.concat(
                TokenDoc.token(SyntaxKind.LBRACE, "{"),
                TokenDoc.HARD_GAP,
                TokenDoc.token(SyntaxKind.LBRACE, "{")));
        assertEquals("{\n{", render(unlisted, WIDE));
    }
}
