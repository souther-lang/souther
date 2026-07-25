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

/**
 * A field the boundary cannot represent is reported on the field, in the type the author wrote.
 * The report used to name the codec that gave up ("cannot derive a list-element encoder for
 * ListOf[element=Ref[name=IssueId]]"), print the internal type, and point at the data's first line,
 * which says nothing about which of a dozen fields is the problem.
 */
class CompileDeriveDiagnosticTest {

    private static Diagnostic diagnosticOf(String src) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        return e.diagnostic();
    }

    @Test
    void aTupleInsideACollectionIsReportedOnTheField() {
        String src = """
                module demo

                data 集計 = {
                    entries: Map<String, (String, Int)>
                }
                """;
        Diagnostic d = diagnosticOf(src);

        assertEquals(4, d.pos().line());
        String out = new HumanRenderer(false).render(d, new SourceContext("demo.sou", src),
                Locale.ENGLISH);
        assertTrue(out.contains("`entries`"), out);
        assertTrue(out.contains("Map<String, (String, Int)>"), out);
        assertTrue(out.contains("Use a named data"), out);

        // the same three parts in Japanese: a locale must not lose the field or the type
        String ja = new HumanRenderer(false).render(d, new SourceContext("demo.sou", src),
                Locale.JAPANESE);
        assertTrue(ja.contains("フィールド `entries`"), ja);
        assertTrue(ja.contains("Map<String, (String, Int)>"), ja);
    }

    @Test
    void aTupleFieldStillReportsItselfWhenItIsNotNested() {
        String src = """
                module demo

                data 座席 = {
                    where: (Int, Int)
                }
                """;
        Diagnostic d = diagnosticOf(src);

        assertEquals(4, d.pos().line());
        String out = new HumanRenderer(false).render(d, new SourceContext("demo.sou", src),
                Locale.ENGLISH);
        assertTrue(out.contains("`where`"), out);
        assertTrue(out.contains("(Int, Int)"), out);
    }
}
