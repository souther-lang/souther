package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A binding may not take the name of a built-in value ({@code None}). That name resolves to the
 * built-in, so shadowing it silently makes it unreachable in that scope — always a mistake, so it
 * is rejected rather than allowed to shadow. A unit data name is ordinary vocabulary and may be
 * bound, the local taking precedence ([#unit-data]) — a rounding-mode case included.
 */
class CompileShadowingTest {

    @Test
    void aLetCannotShadowNone() {
        String src = """
                module demo
                data In = { v: Int }
                data Out = { v: Int }
                behavior check : (o: In) -> Out constructs Out
                let check (o) = {
                    let None = 99
                    Out { v = None }
                }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertTrue(e.getMessage().contains("None"), e.getMessage());
    }

    /** A rounding-mode case is a unit data, so a binding may take its name and is what the name
     * means in that scope. */
    @Test
    void aBindingMayShadowARoundingModeCase() throws Exception {
        String src = """
                module demo
                data In = { v: Int }
                data Out = { v: Int }
                behavior check : (i: In) -> Out constructs Out
                let check (i) = Out { v = twice(i.v) }
                let twice (HALF_UP: Int) = HALF_UP + HALF_UP
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", java.util.Map.of("v", 21L));
        Object check = Emitted.behavior(loader, "demo", "check").getConstructor().newInstance();
        java.util.Map<?, ?> out =
                (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(check, in));
        org.junit.jupiter.api.Assertions.assertEquals(42L, out.get("v"));
    }
}
