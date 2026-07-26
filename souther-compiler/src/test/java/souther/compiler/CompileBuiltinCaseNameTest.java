package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;


import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The cases a partial built-in yields — {@code Int | DivisionByZero} — are named by a primitive and by
 * a runtime-declared case, so neither is a name any module declares. Every place that turns a written
 * case name into a type has to know that, not only the match checker.
 */
class CompileBuiltinCaseNameTest {

    /** An invariant-bearing construction brings the invariant analysis into a body whose match binds
     * a primitive arm ({@code | Int as q}). */
    @Test
    void anInvariantIsAnalysedThroughAMatchOnAPrimitiveHeadedUnion() {
        Compiler.compile("""
                module demo

                import Int ( divide )

                data Amount = Int
                    invariant value >= 0

                behavior half : (a: Int) -> Amount constructs Amount

                let half (a) =
                    match divide(a, 2) with
                        | Int as q -> Amount(q)
                        | DivisionByZero -> Amount(0)
                """);
    }

    /** A fixture naming an arm the target cannot produce is a diagnostic, not a crash. */
    @Test
    void aFixtureArmThatNamesNothingIsReported() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Out = { n: Int }

                behavior twice : (a: Int) -> Out constructs Out
                let twice (a) = Out { n = a * 2 }

                example twice
                    | (3) -> Typo { n = 6 }
                """));

        assertTrue(e.getMessage().contains("Typo"), e.getMessage());
    }
}
