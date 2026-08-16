package souther.compiler.fmt;

import souther.compiler.cst.SyntaxKind;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A skeleton is laid out by the formatter, and where its holes are is read back through the tokens
 * it was built from.
 *
 * <p>Nothing here spells a space or a line break. The tokens are written down, the formatter is
 * given them, and what comes back is the canonical form of exactly those tokens — so a skeleton
 * whose placeholders are left as they stand is already formatted, and stays that way when the file
 * it was written into is next formatted. That is a property of how it is built rather than something
 * to check afterwards.
 *
 * <p>The holes are found by counting tokens, not by looking for their text. A hole's default may be
 * spelled the same as something else in the same skeleton — a parameter named for the behavior it
 * injects, an expected value named for a parameter — and a search for the text would find whichever
 * came first. The count is decided when the skeleton is built and is checked against the formatted
 * text token by token, so a formatter that ever moved, added or rewrote one is refused rather than
 * quietly given a hole in the wrong place.
 */
class ASkeletonKeepsEveryTokenItWasBuiltFromTest {

    /** {@code let f (a, b) = c}, with the parameters and the body as holes. */
    private static List<Skeleton.Part> aLet() {
        return List.of(
                literal(word(SyntaxKind.LET_KW, "let"), word(SyntaxKind.IDENT, "f"),
                        word(SyntaxKind.LPAREN, "(")),
                hole(Skeleton.Category.IDENTIFIER, word(SyntaxKind.IDENT, "a")),
                literal(word(SyntaxKind.COMMA, ",")),
                hole(Skeleton.Category.IDENTIFIER, word(SyntaxKind.IDENT, "b")),
                literal(word(SyntaxKind.RPAREN, ")"), word(SyntaxKind.ASSIGN, "=")),
                hole(Skeleton.Category.EXPRESSION, word(SyntaxKind.IDENT, "c")));
    }

    @Test
    void itIsLaidOutTheWayTheFormatterLaysOutThoseTokens() {
        Skeleton.Built built = Skeleton.of(aLet());
        assertEquals(Formatter.format("let f (a, b) = c"), built.text());
    }

    /** And so formatting it again moves nothing. */
    @Test
    void formattingItAgainChangesNothing() {
        Skeleton.Built built = Skeleton.of(aLet());
        assertEquals(built.text(), Formatter.format(built.text()));
    }

    /** Each hole covers the text it was built from, and carries what kind of hole it is. */
    @Test
    void aHoleCoversTheTokensItWasBuiltFrom() {
        Skeleton.Built built = Skeleton.of(aLet());
        assertEquals(List.of("a", "b", "c"), built.holes().stream()
                .map(hole -> built.text().substring(hole.start(), hole.end())).toList());
        assertEquals(List.of(Skeleton.Category.IDENTIFIER, Skeleton.Category.IDENTIFIER,
                        Skeleton.Category.EXPRESSION),
                built.holes().stream().map(Skeleton.Placed::category).toList());
    }

    /**
     * A hole is where it was built, not where its text next appears.
     *
     * <p>Here the body is spelled the same as the first parameter, which is legal and says nothing
     * about the two being the same thing. A skeleton that looked for its holes would put the third
     * one on the first parameter.
     */
    @Test
    void aHoleIsNotFoundByLookingForItsText() {
        Skeleton.Built built = Skeleton.of(List.of(
                literal(word(SyntaxKind.LET_KW, "let"), word(SyntaxKind.IDENT, "f"),
                        word(SyntaxKind.LPAREN, "(")),
                hole(Skeleton.Category.IDENTIFIER, word(SyntaxKind.IDENT, "a")),
                literal(word(SyntaxKind.RPAREN, ")"), word(SyntaxKind.ASSIGN, "=")),
                hole(Skeleton.Category.EXPRESSION, word(SyntaxKind.IDENT, "a"))));
        assertEquals(2, built.holes().size());
        assertTrue(built.holes().get(0).start() < built.holes().get(1).start(),
                "both holes landed on the same `a`");
        assertEquals("let f (a) = a\n", built.text());
    }

    /** Tokens that do not parse are not a skeleton, and are refused rather than laid out. */
    @Test
    void tokensThatDoNotParseAreRefused() {
        assertThrows(Skeleton.Mismatch.class, () -> Skeleton.of(List.of(
                literal(word(SyntaxKind.LET_KW, "let"), word(SyntaxKind.LPAREN, "(")))));
    }

    /**
     * And a formatted text that is not the tokens it was built from is refused.
     *
     * <p>The correspondence is asked directly here, with a token taken out of the list it is held
     * against, because a formatter that rewrites a skeleton's tokens is the thing this refuses and
     * the formatter does not do it. Without this the refusal would never be exercised, and a
     * correspondence that accepted anything would read as a passing test.
     */
    @Test
    void aFormattedTextThatIsNotThoseTokensIsRefused() {
        List<Skeleton.Word> composed = List.of(word(SyntaxKind.LET_KW, "let"),
                word(SyntaxKind.IDENT, "f"), word(SyntaxKind.ASSIGN, "="),
                word(SyntaxKind.IDENT, "c"));
        assertThrows(Skeleton.Mismatch.class,
                () -> Skeleton.placedIn(composed, "let f =\n", List.of()),
                "a text short of a token was taken for the tokens it was built from");
        assertThrows(Skeleton.Mismatch.class,
                () -> Skeleton.placedIn(composed, "let f = c d\n", List.of()),
                "a text with a token over was taken for the tokens it was built from");
        assertThrows(Skeleton.Mismatch.class,
                () -> Skeleton.placedIn(composed, "let g = c\n", List.of()),
                "a text spelling a token otherwise was taken for the tokens it was built from");
        assertEquals(List.of(), Skeleton.placedIn(composed, "let f = c\n", List.of()),
                "the text that is those tokens was refused");
    }

    private static Skeleton.Word word(SyntaxKind kind, String text) {
        return new Skeleton.Word(kind, text);
    }

    private static Skeleton.Part literal(Skeleton.Word... words) {
        return new Skeleton.Part.Literal(List.of(words));
    }

    private static Skeleton.Part hole(Skeleton.Category category, Skeleton.Word... words) {
        return new Skeleton.Part.Hole(category, List.of(words));
    }
}
