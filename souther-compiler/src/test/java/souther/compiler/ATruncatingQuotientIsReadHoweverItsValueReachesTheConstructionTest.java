package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A truncating quotient is read as one however its value reaches the construction.
 *
 * <p>{@code Int.truncatingDivide} answers a union, so what a model does with the quotient is open:
 * the arm may build from the binding, or hand it back from a helper, or give it a name first. What is
 * known of the quotient is the arithmetic's and must not turn on which of those an author wrote
 * (#959).
 *
 * <p>The operator is not one of the ways. Its quotient is exact and answers a Rational, which is
 * another number and no value of the newtype's base (spec §stdlib-rational), so a construction from
 * it does not type-check — the last row here is what says so.
 *
 * <p>What discharges the construction is one rule: a dividend at or above nought over a
 * positive divisor answers at or above nought (spec §invariant-discharge-arithmetic). The guard,
 * the construction and the divisor are the same in every row, and only the way the value is handed
 * on changes.
 */
class ATruncatingQuotientIsReadHoweverItsValueReachesTheConstructionTest {

    private static String model(String construction) {
        return """
                module demo

                data 硬貨枚数 = Int
                    invariant value >= 0

                let 商 (a: Int, b: Int): Int =
                    match Int.truncatingDivide(a, b) with
                        | Int as n -> n
                        | DivisionByZero -> unreachable "額面は定数で、0にならない"

                behavior 買う : (額: Int) -> 硬貨枚数
                    constructs 硬貨枚数

                let 買う (額) = {
                    guard 額 >= 0 else 硬貨枚数(0)
                    %s
                }
                """.formatted(construction);
    }

    private static List<String> reported(String construction) {
        return Compiler.compileWithWarnings(model(construction)).warnings().stream()
                .map(Diagnostic::code)
                .toList();
    }

    /** The division inside a helper that opens the value case and answers what it bound. The
     * helper is expanded into the body, so what reaches the construction is the arm's binding. */
    @Test
    void aHelperThatOpensTheValueCaseIsRead() {
        assertEquals(List.of(), reported("硬貨枚数(商(額, 10))"));
    }

    /** The arm's binding read straight into the construction. */
    @Test
    void theValueCaseOpenedAtTheConstructionIsRead() {
        assertEquals(List.of(), reported("""
                match Int.truncatingDivide(額, 10) with
                        | Int as n -> 硬貨枚数(n)
                        | DivisionByZero -> 硬貨枚数(0)"""));
    }

    /** The same, given a name first. Naming a value does not change what is known of it. */
    @Test
    void theValueCaseGivenANameIsRead() {
        assertEquals(List.of(), reported("""
                {
                        let q = match Int.truncatingDivide(額, 10) with
                            | Int as n -> n
                            | DivisionByZero -> 0
                        硬貨枚数(q)
                    }"""));
    }

    /**
     * The control. Nothing puts the dividend at or above nought, so the quotient runs either way and
     * the construction is owed its clause — which is what says the rows above are the rule being read
     * and not a reader that discharges whatever it is handed.
     */
    @Test
    void withNothingKnownOfTheDividendTheClauseIsStillOwed() {
        assertEquals(List.of("E2011"),
                reported("硬貨枚数(商(額 - 1000000, 10))").stream().distinct().toList());
    }

    /**
     * And the operator is no spelling of this quotient. What it answers is exact, and the newtype
     * wraps an {@code Int}, so the construction is refused where it is written rather than read as the
     * truncating one (spec §stdlib-rational).
     */
    @Test
    void theOperatorAnswersAnotherNumberAndDoesNotReachTheConstruction() {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileWithWarnings(model("硬貨枚数(額 / 10)")));
        assertTrue(refused.getMessage().contains("Rational"), refused.getMessage());
    }
}
