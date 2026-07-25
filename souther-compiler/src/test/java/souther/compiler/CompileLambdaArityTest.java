package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;
import org.junit.jupiter.api.Test;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** A lambda given to a combinator is registered under a synthetic name while it is inlined. A wrong
 * number of parameters must be reported against the parameter it fills, not against that internal
 * name. */
class CompileLambdaArityTest {

    @Test
    void aLambdaWithTooManyParametersNamesTheCombinatorParameter() {
        String src = """
                module demo
                data Names = { ns: List<String> }
                data Count = { n: Int }
                behavior count : (m: Names) -> Count constructs Count

                let count (m) = Count { n = List.length(List.map((k, v) -> k, m.ns)) }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        String rendered = new HumanRenderer(false).render(e.diagnostic(), null, Locale.ENGLISH);
        assertFalse(rendered.contains("$"), "internal lambda name leaked:\n" + rendered);
        assertTrue(rendered.contains("`f`"), rendered);
        assertTrue(rendered.contains("let map"), rendered);
    }
}
