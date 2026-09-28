package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A {@code >->} composition the {@code exposing} clause names must declare its output there
 * ({@code exposing ( name : A | B )}, spec §declared-composition-output), and the declaration must
 * match the inferred output exactly. This is the boundary a module states, where a far-away case
 * addition would otherwise reach separately-compiled consumers unannounced. The requirement is on
 * that statement only: a composition the clause does not name keeps inference, whether it is kept
 * or published because no clause is written, and a signature on a non-composition is rejected.
 */
class CompileExposedPipeOutputTest {

    /** {@code capAmount} retires {@code TooLarge}; {@code toDoubled} yields {@code Doubled}, so
     * {@code process = capAmount >-> toDoubled} produces {@code Doubled | TooLarge}. */
    private static String mod(String exposing) {
        return "module demo exposing ( Amount, %s )\n".formatted(exposing) + DECLARATIONS;
    }

    private static final String DECLARATIONS = """

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
                """;

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

    /** A module writing no clause publishes `process`, but no clause names it, so it states no
     *  boundary and its output stays inferred (spec §a-module-publishes-what-it-declares). */
    @Test
    void aCompositionPublishedByWritingNoClauseNeedsNoSignature() {
        assertDoesNotThrow(() -> Compiler.compile("module demo\n" + DECLARATIONS));
    }
}
