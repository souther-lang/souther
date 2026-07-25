package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.SourceContext;

import org.junit.jupiter.api.Test;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Reading a field off a sum is a compile error — a sum has no fields of its own, and which case it is
 * is not known until it is opened. `...include` flattens into each case, so every case can carry the
 * same field and the sum still has none. The report says that, rather than "cannot access field `f`
 * on this value", which leaves the author to guess what the value even was.
 */
class CompileSumFieldAccessTest {

    private static String rendered(String src, Locale locale) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        Diagnostic d = e.diagnostic();
        return new HumanRenderer(false).render(d, new SourceContext("demo.sou", src), locale);
    }

    @Test
    void aFieldEveryCaseSharesIsStillReadThroughMatch() {
        String src = """
                module demo

                data 共通 = { タイトル: String }
                data A = { ...共通, x: Int }
                data B = { ...共通, y: Int }
                data S = A | B
                data Out = { t: String }

                behavior run : (s: S) -> Out constructs Out

                let run (s) = Out { t = s.タイトル }
                """;
        String out = rendered(src, Locale.ENGLISH);

        assertTrue(out.contains("`タイトル`"), out);
        assertTrue(out.contains("`S`"), out);                  // which value it was
        assertTrue(out.contains("`match`"), out);              // what to write instead
        assertFalse(out.contains("These cases have no"), out); // every case has it, so no such hint
    }

    @Test
    void theCasesMissingTheFieldAreNamed() {
        String src = """
                module demo

                data A = { タイトル: String }
                data B = { y: Int }
                data S = A | B
                data Out = { t: String }

                behavior run : (s: S) -> Out constructs Out

                let run (s) = Out { t = s.タイトル }
                """;
        String out = rendered(src, Locale.ENGLISH);

        assertTrue(out.contains("These cases have no `タイトル` field: B"), out);
    }

    @Test
    void theJapaneseReportCarriesTheSameThreeParts() {
        String src = """
                module demo

                data 共通 = { タイトル: String }
                data A = { ...共通, x: Int }
                data B = { ...共通, y: Int }
                data S = A | B
                data Out = { t: String }

                behavior run : (s: S) -> Out constructs Out

                let run (s) = Out { t = s.タイトル }
                """;
        String out = rendered(src, Locale.JAPANESE);

        assertTrue(out.contains("`タイトル`"), out);
        assertTrue(out.contains("`S`"), out);
        assertTrue(out.contains("`match`"), out);
    }

    @Test
    void aValueThatIsNotADataKeepsThePlainReport() {
        String src = """
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { n = i.n.missing }
                """;
        String out = rendered(src, Locale.ENGLISH);

        assertTrue(out.contains("`missing`"), out);
        assertFalse(out.contains("sum"), out);
    }
}
