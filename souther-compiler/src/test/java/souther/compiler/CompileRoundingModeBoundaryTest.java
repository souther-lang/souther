package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code RoundingMode} is ordinary data for typing, evaluation, composition and ordering, but it
 * provides no codec, so it cannot appear where a codec is required. The absence is intentional: a
 * rounding policy is a computation's input, not a value that crosses a serialization boundary, and
 * these tests pin the refusal so the type never quietly gains an external representation.
 */
class CompileRoundingModeBoundaryTest {

    /** A field of {@code RoundingMode} would need its decoder and encoder, and it has neither. */
    @Test
    void aFieldOfRoundingModeIsRefusedForItsMissingCodec() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Policy = { mode: RoundingMode }
                """));
        assertEquals("check.codec.nodecoder", e.diagnostic().messageKey());
        assertTrue(e.getMessage().contains("RoundingMode"), e.getMessage());
    }

    /** An example fixture would have to decode the mode, and there is no decoder to call. */
    @Test
    void anExampleOverARoundingModeParameterIsRefused() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Out = { n: Int }

                behavior g : (m: RoundingMode, d: Decimal) -> Out constructs Out
                let g (m, d) = Out { n = Decimal.toInt(m, d) }

                example g
                    | "rounds up at the half" :
                        (HALF_UP, 2.5m) -> Out { n = 3 }
                """));
        assertTrue(e.getMessage().contains("E1903"), e.getMessage());
        assertTrue(e.getMessage().contains("no decoder for `RoundingMode`"), e.getMessage());
    }
}
