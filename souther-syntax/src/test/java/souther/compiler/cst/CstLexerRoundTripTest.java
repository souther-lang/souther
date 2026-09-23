package souther.compiler.cst;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The lossless invariant of the trivia-preserving lexer: concatenating every token's text (trivia,
 * comments, and error tokens included) reproduces the source exactly. This is the property the
 * formatter and incremental reparse rest on, so it is exercised over a set of tricky literals. The
 * bundled prelude is swept by {@link CstParserRoundTripTest}, whose tree is built from these tokens
 * and reproduces the source only where they do.
 */
class CstLexerRoundTripTest {

    private static String relex(String source) {
        StringBuilder sb = new StringBuilder();
        for (GreenToken t : CstLexer.lex(source).tokens()) {
            sb.append(t.text());
        }
        return sb.toString();
    }

    @ParameterizedTest
    @ValueSource(strings = {
            "",
            "module A",
            "// just a comment\n",
            "data X = String\n    invariant length(value) > 0\n",
            "let f (x) = x |> g |> h",
            "\"a\\nb\\t\\\"c\"",              // escapes stay raw in the token text
            "500m + 1.5m - 3",
            "x -> x ++ \"!\"",
            "a >-> b >-> c",
            "match x with | A -> 1 | B as y -> 2",
            "Map<String, List<T>>",
            "  \r\n\t  leading trivia",
            "trailing trivia   \n\n",
            "unexpected # char",           // an unknown char becomes an ERROR_TOKEN, still lossless
            "\"unterminated",              // an unterminated string still covers to EOF
    })
    void relexingReproducesTheSource(String source) {
        assertEquals(source, relex(source));
    }

    @Test
    void everyOffsetIsCoveredExactlyOnceInOrder() {
        String source = "let f (x) = x + 1  // tail\n";
        List<GreenToken> tokens = CstLexer.lex(source).tokens();
        int at = 0;
        for (GreenToken t : tokens) {
            assertEquals(source.substring(at, at + t.width()), t.text());
            at += t.width();
        }
        assertEquals(source.length(), at);
        assertTrue(tokens.get(tokens.size() - 1).kind() == SyntaxKind.EOF);
    }
}
