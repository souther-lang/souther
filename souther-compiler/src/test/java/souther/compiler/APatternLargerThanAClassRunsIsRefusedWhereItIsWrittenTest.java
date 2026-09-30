package souther.compiler;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.decode.Decoder;
import souther.compiler.cst.SourceLayout;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.SourceContext;

import org.junit.jupiter.api.Test;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A pattern is run as a machine a class holds, and a pattern whose machine is past what a class runs
 * is refused rather than handed to anything else to run (spec
 * {@code [#a-pattern-runs-as-a-machine-a-class-holds]}).
 *
 * <p>Refused where the pattern is: a {@code String.matches} call at its pattern, and a decoder's
 * format at the data whose clause it was read from. A pattern whose deterministic machine is
 * large and whose shape is small is not refused; that it runs is
 * {@code WhatARunWalksIsWhatThePatternMeansTest}'s.
 */
class APatternLargerThanAClassRunsIsRefusedWhereItIsWrittenTest {

    private static final String TOO_LARGE = "(a{1000}){100}";

    @Test
    void aCallsPatternIsRefusedAtThePattern() {
        String src = """
                module demo
                data In = { s: String }
                data Out = Bool
                behavior check : (i: In) -> Out constructs Out
                let check (i) =
                    Out(String.matches("%s", i.s))
                """.formatted(TOO_LARGE);
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E2109", e.code(), e.getMessage());

        String said = rendered(e, src);
        assertTrue(said.contains("demo.sou:6:24"), "at the pattern: " + said);
        assertTrue(said.contains(TOO_LARGE), "quoting what was written: " + said);
    }

    @Test
    void aFormatAtTheBoundaryIsRefusedToo() {
        String src = """
                module demo
                data Code = String invariant String.matches("%s", value)
                """.formatted(TOO_LARGE);
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E2109", e.code(), e.getMessage());
        assertTrue(rendered(e, src).contains("demo.sou:2:"), rendered(e, src));
    }

    /** And a class loads it and runs it: the decoder holds its value to it. */
    @Test
    void aPatternTooLargeToMakeDeterministicIsNotRefused() throws Exception {
        ClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo
                data Code = String invariant String.matches(".*a.{20}", value)
                """), getClass().getClassLoader());
        Decoder<Object, ?> code = Codecs.decoder(loader, "demo.Code");
        assertInstanceOf(Ok.class, code.decode("xa" + "b".repeat(20), Path.ROOT));
        assertInstanceOf(Err.class, code.decode("xa" + "b".repeat(19), Path.ROOT));
    }

    private static String rendered(CompileException e, String src) {
        return new HumanRenderer(false).render(e.diagnostic(),
                new SourceContext("demo.sou", src, SourceLayout.of(src)), Locale.ENGLISH);
    }
}
