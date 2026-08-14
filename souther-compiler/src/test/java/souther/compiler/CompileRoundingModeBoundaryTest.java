package souther.compiler;

import souther.compiler.diag.msg.TypeMessage;
import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code RoundingMode} is ordinary data for typing, evaluation, composition and ordering, and it is
 * the language's own vocabulary — it says what {@code Decimal.round} takes. A rounding policy is a
 * computation's input rather than a value a model publishes, so it is refused wherever an external
 * representation crosses: at a behavior's boundary, and in a data field, which crosses too. These
 * tests pin that refusal so the type never quietly gains an external representation.
 *
 * <p>The field was refused for having no codec, which is a different sentence about the same
 * spelling: it named a mechanism the author never wrote and, said that way, it also refused a unit
 * data — the model's own word, with a codec its class is generated with. Whose vocabulary the name
 * is, is what decides both.
 */
class CompileRoundingModeBoundaryTest {

    /** A field is a position an external representation crosses, so the rule reaches it. */
    @Test
    void aFieldOfRoundingModeIsRefusedForWhoseVocabularyItIs() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Policy = { mode: RoundingMode }
                """));
        assertInstanceOf(TypeMessage.AFieldTakesATypeTheLanguageDeclares.class,
                e.diagnostic().said());
        assertTrue(e.getMessage().contains("E1325"), e.getMessage());
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
