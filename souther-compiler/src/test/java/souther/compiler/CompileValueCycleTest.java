package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value is substituted at each reference, so a value that reaches itself has nothing to be
 * substituted with. A helper on a call cycle is lowered to a method and recurses at run time; a value
 * has no such form, and the two are reported apart — a value cycle that fell through to the recursion
 * check would be told to declare a return type it never had.
 */
class CompileValueCycleTest {

    private static CompileException refused(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source));
    }

    private static final String FRAME = """
            module demo

            data In = { n: Int }
            data Out = { n: Int }

            %s

            behavior go : (i: In) -> Out constructs Out
            let go (i) = Out { n = i.n + step }
            """;

    @Test
    void aValueMayNotReferToItself() {
        CompileException e = refused(FRAME.formatted("let step = step"));

        assertTrue(e.getMessage().contains("step"), e.getMessage());
        assertTrue(e.getMessage().contains("itself") || e.getMessage().contains("cycle"),
                e.getMessage());
    }

    @Test
    void valuesMayNotReferToEachOtherCyclically() {
        CompileException e = refused(FRAME.formatted("""
                let step = other
                let other = step"""));

        assertTrue(e.getMessage().contains("step") && e.getMessage().contains("other"),
                e.getMessage());
    }

    @Test
    void aLongerValueCycleIsReportedWithTheWholePath() {
        CompileException e = refused(FRAME.formatted("""
                let step = middle
                let middle = last
                let last = step"""));

        assertTrue(e.getMessage().contains("middle") && e.getMessage().contains("last"),
                e.getMessage());
    }

    /** A value nothing names still cannot be defined in terms of itself: the definition is what is
     * wrong, not the use. */
    @Test
    void aValueCycleIsReportedEvenWhereNothingNamesIt() {
        CompileException e = refused("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let step = other
                let other = step

                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { n = i.n }
                """);

        assertTrue(e.getMessage().contains("step"), e.getMessage());
    }

    /** A cycle that runs through a helper call is still a value cycle: the value has no method to be
     * lowered to, so the recursion the helper is allowed does not rescue it. */
    @Test
    void aCycleThroughAHelperCallIsAValueCycle() {
        CompileException e = refused("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let step = twice(1)
                let twice (n) = n * step

                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { n = i.n + step }
                """);

        assertTrue(e.getMessage().contains("step"), e.getMessage());
    }

    /** A helper on a call cycle is untouched by this: it is lowered to a method and recurses. */
    @Test
    void aRecursiveHelperIsNotAValueCycle() {
        CompileException e = refused("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let countDown (n: Int) : Int = countDown(n - 1)

                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { n = countDown(i.n) }
                """);

        // reported by the totality check, under its own name, not as a value cycle
        assertTrue(e.getMessage().contains("structurally recursive"), e.getMessage());
    }
}
