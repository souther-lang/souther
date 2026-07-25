package souther.compiler;

import souther.compiler.diag.CompileException;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.SourceContext;

import org.junit.jupiter.api.Test;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** Syntax errors: every parser/lexer error carries the SYNTAX ERROR title, reports token kinds by a
 * reader-facing name (`:`, a name — not COLON/IDENT), and localizes both the message and the token
 * category. */
class SyntaxDiagnosticTest {

    private static Diagnostic diagnosticOf(String src) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        return e.diagnostic();
    }

    @Test
    void everyParserErrorCarriesTheSyntaxTitle() {
        // a bespoke error (fn is not a top-level keyword) and a generic expect error both get it
        assertEquals("parse.title", diagnosticOf("module demo\nfn f (x) = x\n").titleKey());
        assertEquals("parse.title", diagnosticOf("module demo\ndata M = { name String }\n").titleKey());
    }

    @Test
    void expectedFoundUsesFriendlyTokenNamesAndLocalizes() {
        Diagnostic d = diagnosticOf("module demo\ndata M = { name String }\n");
        assertEquals("parse.expected", d.messageKey());
        SourceContext src = new SourceContext("m.sou", "module demo\ndata M = { name String }\n");
        String en = new HumanRenderer(false).render(d, src, Locale.ENGLISH);
        String ja = new HumanRenderer(false).render(d, src, Locale.JAPANESE);
        assertTrue(en.contains("I expected `:` here, but found a name."), en);
        assertTrue(ja.contains("`:`") && ja.contains("名前"), ja);
        assertTrue(en.contains("SYNTAX ERROR") && ja.contains("構文エラー"));
    }

    @Test
    void aBlockOfOnlyStatementsIsASyntaxError() {
        Diagnostic d = diagnosticOf("""
                module demo
                let run (i) = {
                    let a = i
                }
                """);
        assertEquals("parse.title", d.titleKey());
        assertEquals("parse.block.noresult", d.messageKey());
    }

    // Issue #75: `i` and the following line's `(a)` read as one call, so the block is left with no
    // result. It used to reach the AST builder and die with a NullPointerException; the message says
    // what happened, in both locales.
    @Test
    void aResultAbsorbedByTheLineAboveIsReportedRatherThanCrashing() {
        String source = """
                module demo
                let run (i) = {
                    let a = i
                    (a)
                }
                """;
        Diagnostic d = diagnosticOf(source);
        assertEquals("parse.block.noresult", d.messageKey());
        SourceContext src = new SourceContext("m.sou", source);
        String en = new HumanRenderer(false).render(d, src, Locale.ENGLISH);
        String ja = new HumanRenderer(false).render(d, src, Locale.JAPANESE);
        assertTrue(en.contains("A block ends in one expression, which is its value"), en);
        assertTrue(ja.contains("ブロックは最後に値となる式を1つ置きます"), ja);
    }

    @Test
    void lexerErrorIsLocalized() {
        Diagnostic d = diagnosticOf("module demo\ndata M = Int\nlet x = 1.5\n");
        assertEquals("parse.title", d.titleKey());
        assertEquals("lex.decimal.m", d.messageKey());
    }
}
