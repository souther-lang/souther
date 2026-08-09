package souther.compiler;

import souther.compiler.diag.msg.CodecMessage;
import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code RoundingMode} is ordinary data for typing, evaluation, composition and ordering, but it
 * provides no codec, so it cannot appear where a codec is required. The absence is intentional: a
 * rounding policy is a computation's input, not a value that crosses a serialization boundary, and
 * these tests pin the refusal so the type never quietly gains an external representation. It is also
 * the language's own vocabulary — it says what {@code Decimal.round} takes — which is what a
 * behavior's boundary is refused for, and that refusal comes first.
 */
class CompileRoundingModeBoundaryTest {

    /** A field of {@code RoundingMode} would need its decoder and encoder, and it has neither. */
    @Test
    void aFieldOfRoundingModeIsRefusedForItsMissingCodec() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Policy = { mode: RoundingMode }
                """));
        assertInstanceOf(CodecMessage.HasNoDecoder.class, e.diagnostic().said());
        assertTrue(e.getMessage().contains("RoundingMode"), e.getMessage());
    }

    /**
     * A behavior taking the mode is refused where it is declared, not later. It used to compile and
     * fail only where something asked for the decoder — an example fixture, or `souther run` reaching
     * for it by reflection — so what a reader was shown depended on what they happened to write next.
     */
    @Test
    void aBehaviorTakingARoundingModeIsRefusedAtItsSignature() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Out = { n: Int }

                behavior g : (m: RoundingMode, d: Decimal) -> Out constructs Out
                let g (m, d) = Out { n = Decimal.toInt(m, d) }

                example g
                    | "rounds up at the half" :
                        (HALF_UP, 2.5m) -> Out { n = 3 }
                """));
        assertTrue(e.getMessage().contains("E1325"), e.getMessage());
        assertTrue(e.getMessage().contains("RoundingMode"), e.getMessage());
    }
}
