package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An exposed {@code >->} composition must declare its output in the {@code exposing} list
 * ({@code exposing ( name : A | B )}, spec 14.5, ADR-0024), and the declaration must match the
 * inferred output exactly. This is the module boundary where a far-away case addition would
 * otherwise reach separately-compiled consumers unannounced. The requirement is boundary-only:
 * an unexposed composition keeps inference, and a signature on a non-composition is rejected.
 */
class CompileExposedPipeOutputTest {

    /** {@code capAmount} retires {@code TooLarge}; {@code toDoubled} yields {@code Doubled}, so
     * {@code process = capAmount >-> toDoubled} produces {@code Doubled | TooLarge}. */
    private static String mod(String exposing) {
        return """
                module demo exposing ( Amount, %s )

                data Amount = Int
                data TooLarge = { limit: Int }
                data Doubled = Int

                behavior capAmount : (a: Amount) -> Amount | TooLarge constructs TooLarge
                let capAmount (a) = {
                    guard a.value <= 100 else TooLarge { limit = 100 }
                    a
                }

                behavior toDoubled : (a: Amount) -> Doubled constructs Doubled
                let toDoubled (a) = Doubled { value = a.value }

                behavior process = capAmount >-> toDoubled
                """.formatted(exposing);
    }

    @Test
    void exposedCompositionWithMatchingSignatureCompiles() {
        assertDoesNotThrow(() -> Compiler.compile(mod("process : Doubled | TooLarge")));
    }

    @Test
    void exposedCompositionWithoutSignatureIsE1605() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(mod("process")));
        assertEquals("E1605", e.code());
    }

    @Test
    void exposedCompositionWithTooNarrowSignatureIsE1604() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(mod("process : Doubled")));
        assertEquals("E1604", e.code());
    }

    @Test
    void aSignatureOnANonCompositionIsE1605() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(mod("capAmount : Amount")));
        assertEquals("E1605", e.code());
    }

    @Test
    void anUnexposedCompositionNeedsNoSignature() {
        // `process` is defined but not exposed, so inference stands and no signature is required.
        assertDoesNotThrow(() -> Compiler.compile(mod("Doubled")));
    }
}
