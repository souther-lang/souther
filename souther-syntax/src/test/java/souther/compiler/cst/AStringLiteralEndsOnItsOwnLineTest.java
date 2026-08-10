package souther.compiler.cst;

import souther.compiler.diag.msg.ParseMessage;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a string literal may be, held against the lexer that decides it.
 *
 * <p>Two rules, and each is about what the reader is told rather than only about what is refused.
 * A literal that ran past its line took the rest of the file into itself and reported the loss
 * wherever it finally stopped, so the one missing quote was answered somewhere it was not. A
 * backslash before something that is not an escape used to be read as the character alone, which
 * took a character the author wrote out of the value and said nothing.
 *
 * <p>The last test is the positive control: the five escapes still read, so a refusal here is a
 * refusal of what the rule names and not of every backslash.
 */
class AStringLiteralEndsOnItsOwnLineTest {

    private static List<String> saidBy(String src) {
        return CstLexer.lex(src).errors().stream()
                .map(error -> error.said().getClass().getSimpleName())
                .toList();
    }

    private static List<String> literalsOf(String src) {
        return CstLexer.lex(src).tokens().stream()
                .filter(token -> token.kind() == SyntaxKind.STRING_LIT)
                .map(GreenToken::text)
                .toList();
    }

    @Test
    void aQuoteMissingBeforeTheNewlineIsSaidAtThatLine() {
        String src = """
                let a = "one
                let b = 1
                """;
        assertEquals("AStringLiteralIsNotClosed", saidBy(src).getFirst());
        assertEquals("\"one", literalsOf(src).getFirst());
    }

    @Test
    void aBackslashDoesNotCarryTheLiteralOverTheNewline() {
        String src = "let a = \"one\\\nlet b = 1\n";
        assertEquals("AStringLiteralIsNotClosed", saidBy(src).getFirst());
        assertEquals("\"one\\", literalsOf(src).getFirst());
    }

    @Test
    void aBackslashBeforeSomethingThatIsNotAnEscapeIsRefusedAndNamed() {
        List<ParseMessage.AnEscapeIsNotOneTheLanguageReads> said =
                CstLexer.lex("let a = \"a\\qb\"\n").errors().stream()
                        .map(error -> error.said())
                        .filter(ParseMessage.AnEscapeIsNotOneTheLanguageReads.class::isInstance)
                        .map(ParseMessage.AnEscapeIsNotOneTheLanguageReads.class::cast)
                        .toList();
        assertEquals(1, said.size());
        assertEquals("q", said.getFirst().escaped());
    }

    @Test
    void theFiveEscapesAreRead() {
        String src = "let a = \"n\\nt\\tr\\rq\\\"b\\\\\"\n";
        assertEquals(List.of(), saidBy(src));
        assertEquals(1, literalsOf(src).size());
    }
}
