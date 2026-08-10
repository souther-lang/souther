package souther.compiler.cst;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A {@code <} and the negation after it are read as that, whether or not a space stands between
 * them.
 *
 * <p>A lexer taking {@code <-} for one token is enough to stop that: a longer match wins, so
 * {@code a<-1} cannot be a comparison against a negative one. With no production reading such a
 * token, what it decides is not how the text reads but whether it reads at all — {@code a < -1}
 * accepted and {@code a<-1} refused, over a form the language does not have.
 *
 * <p>The token sequences are compared, not just the two verdicts. A space is trivia, so the two
 * spellings have to reach the parser as the same tokens; asserting only that both are accepted
 * would still pass if some later rule happened to rescue one of them.
 */
class ALessThanIsNotGluedToTheMinusAfterItTest {

    private static final String MODULE = "module M\n\nlet g (a, b) = ";

    /** The meaningful tokens of a source, trivia and end of input dropped. */
    private static List<SyntaxKind> kinds(String source) {
        return CstLexer.lex(source).tokens().stream()
                .map(GreenToken::kind)
                .filter(kind -> !kind.isTrivia() && kind != SyntaxKind.EOF)
                .toList();
    }

    @ParameterizedTest(name = "{0}")
    @CsvSource(delimiterString = "||", value = {
            "a<-1                  || a < -1",
            "a<-b                  || a < -b",
            "if a<-1 then 0 else 1 || if a < -1 then 0 else 1",
    })
    void theSpaceChangesNothing(String tight, String spaced) {
        assertEquals(kinds(MODULE + spaced + "\n"), kinds(MODULE + tight + "\n"),
                "a space is trivia, so nothing the parser sees may turn on it");
        assertEquals(List.of(), CstParser.parse(MODULE + tight + "\n").errors(),
                "a comparison against a negation is accepted when written without a space");
    }

    @Test
    void noSingleTokenIsSpelledWithALessThanAndAMinus() {
        assertEquals(List.of(SyntaxKind.LT, SyntaxKind.MINUS), kinds("<-"),
                "`<-` is not a form the language has, so it is two tokens");
    }
}
