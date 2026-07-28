package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every name in an {@code exposing} clause must resolve to a data or behavior of the module, and
 * the clause is type-granular: a data's {@code decoder}/{@code encoder} are always public once the
 * data is exposed (spec 4, 19.4), so a {@code A.decoder} member is rejected. A typo used to be
 * accepted silently — exposing nothing — which quietly left a type package-private.
 */
class CompileExposingTest {

    @Test
    void anExposedNameThatDoesNotExistIsRejected() {
        assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                exposing ( NoSuchType )
                data Real = { v: Int }
                """));
    }

    @Test
    void aDecoderMemberInExposingIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                exposing ( Real.decoder )
                data Real = { v: Int }
                """));
        assertTrue(e.getMessage().contains("type-granular"), e.getMessage());
    }

    /**
     * A helper is defined right there in the file, so "not a data or behavior of this module" sends
     * the author looking for a typo they did not make. It is the first thing someone carrying Elm's
     * `exposing (toRate)` habit writes, and what they have to be told is that a pure rule meant to be
     * shared is declared as a behavior (ADR-0005, ADR-0068).
     */
    @Test
    void exposingAHelperSaysToDeclareItAsABehavior() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                exposing ( Real, rateOf )
                data Real = { v: Int }
                let rateOf (r: Real): Int = r.v * 2
                """));
        assertTrue(e.getMessage().contains("helper"), e.getMessage());
        assertTrue(e.getMessage().contains("declare it as a behavior"), e.getMessage());
    }

    @Test
    void realExposedNamesAreAccepted() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                exposing ( Real, Out, greet )

                data Real = { v: Int }
                data Out = { v: Int }

                behavior greet : (r: Real) -> Out constructs Out
                let greet (r) = Out { v = r.v }
                """));
    }
}
