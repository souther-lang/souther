package souther.compiler.cst;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a comment is, held against the lexer that decides it.
 *
 * <p>The specification writes comments in its own samples and had never said what one is. What
 * bounds a comment, and that {@code /*} begins nothing, are facts about the scan and about no set
 * the compiler enumerates, so they are held here rather than derived.
 */
class ACommentRunsToTheEndOfItsLineTest {

    private static List<String> kindsOf(String src) {
        return CstLexer.lex(src).tokens().stream()
                .filter(token -> token.kind() != SyntaxKind.WHITESPACE
                        && token.kind() != SyntaxKind.EOF)
                .map(token -> token.kind() + "(" + token.text() + ")")
                .toList();
    }

    @Test
    void theLineEndsTheCommentAndTheNextOneStillReads() {
        assertEquals(List.of("LET_KW(let)", "IDENT(a)", "ASSIGN(=)", "INT_LIT(1)",
                        "LINE_COMMENT(// note)", "LET_KW(let)", "IDENT(b)", "ASSIGN(=)", "INT_LIT(2)"),
                kindsOf("""
                        let a = 1 // note
                        let b = 2
                        """));
    }

    @Test
    void thereIsNoBlockComment() {
        assertEquals(List.of("SLASH(/)", "STAR(*)", "IDENT(note)", "STAR(*)", "SLASH(/)"),
                kindsOf("/* note */\n"));
    }

    @Test
    void aCommentInsideALiteralBelongsToTheLiteral() {
        assertEquals(List.of("LET_KW(let)", "IDENT(a)", "ASSIGN(=)", "STRING_LIT(\"x//y\")"),
                kindsOf("""
                        let a = "x//y"
                        """));
    }
}
