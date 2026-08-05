package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An unknown name that is a near-miss of a name in scope gets a "did you mean" hint, so a typo is
 * reported as a typo rather than passed on as some other, more confusing failure — a mistyped
 * behavior in a pipeline, for one, would otherwise read as an unknown-behavior dead end.
 */
class CompileDidYouMeanTest {

    private static CompileException compileFail(String src) {
        return assertThrows(CompileException.class, () -> Compiler.compile(src));
    }

    @Test
    void suggestsANearbyType() {
        CompileException e = compileFail("""
                module demo
                data Price = Int
                data Order = { amount: Prise }
                """);
        assertTrue(e.getMessage().contains("did you mean `Price`?"), e.getMessage());
    }

    @Test
    void suggestsANearbyBehaviorInAPipeline() {
        CompileException e = compileFail("""
                module demo
                data N = Int
                behavior inc : (n: N) -> N
                let inc (n) = n
                behavior flow = inc >-> imc
                """);
        assertTrue(e.getMessage().contains("did you mean `inc`?"), e.getMessage());
    }

    @Test
    void suggestsANearbyIdentifier() {
        CompileException e = compileFail("""
                module demo
                import Int ( add )
                data N = Int
                behavior twice : (num: N) -> N constructs N
                let twice (num) = N { value = add(nums.value, num.value) }
                """);
        assertTrue(e.getMessage().contains("did you mean `num`?"), e.getMessage());
    }

    /** A bare standard-library name is reported with the qualified form to write instead. When more
     * than one module defines the name, every one of them is named: the hint must not depend on the
     * order the prelude modules happen to load in. */
    @Test
    void aBareStdlibNameNamesEveryModuleThatDefinesIt() {
        CompileException e = compileFail("""
                module demo
                data In = { xs: List<Int> }
                data Out = { kept: List<Int> }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { kept = filter(n -> n > 0, i.xs) }
                """);
        assertTrue(e.getMessage().contains("`List.filter` or `Set.filter`"), e.getMessage());
    }

    @Test
    void anUnrelatedNameGetsNoHint() {
        CompileException e = compileFail("""
                module demo
                data Price = Int
                data Order = { amount: Xyzzy }
                """);
        assertTrue(e.getMessage().contains("unknown type"), e.getMessage());
        assertTrue(!e.getMessage().contains("did you mean"), e.getMessage());
    }
}
