package souther.compiler.cst;

import souther.compiler.diag.msg.ParseMessage;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    /**
     * The literal written for a string is one this scan reads, whole and without a word, back to the
     * same string.
     *
     * <p>Every text a writer of a literal is handed: the plain, each character that has an escape,
     * a carriage return no line feed follows and one that it does — the second a line terminator
     * written as itself would end — and text beyond the first plane.
     */
    @Test
    void theLiteralWrittenForAStringReadsBackAsThatString() {
        for (String text : List.of("", "plain", "a\"b", "back\\slash", "\\\"", "line\nbreak",
                "cr\ronly", "crlf\r\n", "tab\t", "日本語 😀")) {
            String written = CstLexer.literalOf(text);
            String src = "let a = " + written + "\n";
            assertEquals(List.of(), saidBy(src), () -> "the scan refuses " + written);
            assertEquals(List.of(written), literalsOf(src),
                    () -> "the literal is one token, ending where it was written to: " + written);
            assertEquals(text, CstLexer.textOf(written), () -> "and denotes the text: " + written);
        }
    }

    /** And every backslash the writer puts in is one the scan names as an escape, over every
     *  character below the first non-ASCII one. */
    @Test
    void theWriterEscapesOnlyWhatTheScanReadsAsAnEscape() {
        StringBuilder every = new StringBuilder();
        for (char c = 0; c < 128; c++) {
            every.append(c);
        }
        String written = CstLexer.literalOf(every.toString());
        for (int i = 1; i < written.length() - 1; i++) {
            if (written.charAt(i) == '\\') {
                String escaped = String.valueOf(written.charAt(++i));
                assertTrue(CstLexer.escapes().contains(escaped),
                        () -> "a backslash before " + escaped + ", which the scan does not read");
            }
        }
        assertEquals(every.toString(), CstLexer.textOf(written));
    }
}
