package souther.compiler;

import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A truncating division is read as a quotient through every spelling the language has for it.
 *
 * <p>{@code /} aborts on a zero divisor and {@code Int.divide} answers one as a case, and they
 * compute one number (spec §stdlib-int). Which of the two an author writes is settled by whether
 * the model admits a zero divisor, so the second is what a domain writes wherever the divisor is not
 * a literal it can argue about — and what was known of the quotient turned on the spelling rather
 * than on the arithmetic (#959).
 *
 * <p>What discharges the construction here is one rule: a dividend at or above nought over a
 * positive divisor answers at or above nought (spec §invariant-discharge-arithmetic). The guard,
 * the construction and the divisor are the same in every row, and only the way the division is
 * written changes.
 */
class OneDivisionIsAQuotientHoweverItIsSpelledTest {

    private static String model(String construction) {
        return """
                module demo

                data 硬貨枚数 = Int
                    invariant value >= 0

                let 商 (a: Int, b: Int): Int =
                    match Int.divide(a, b) with
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

    /** The operator, which is the row the rule was written for. */
    @Test
    void theOperatorIsRead() {
        assertEquals(List.of(), reported("硬貨枚数(額 / 10)"));
    }

    /** The same division inside a helper that opens the value case and answers what it bound. The
     * helper is expanded into the body, so what reaches the construction is the arm's binding. */
    @Test
    void aHelperThatOpensTheValueCaseIsRead() {
        assertEquals(List.of(), reported("硬貨枚数(商(額, 10))"));
    }

    /** The arm's binding read straight into the construction. */
    @Test
    void theValueCaseOpenedAtTheConstructionIsRead() {
        assertEquals(List.of(), reported("""
                match Int.divide(額, 10) with
                        | Int as n -> 硬貨枚数(n)
                        | DivisionByZero -> 硬貨枚数(0)"""));
    }

    /** The same, given a name first. Naming a value does not change what is known of it. */
    @Test
    void theValueCaseGivenANameIsRead() {
        assertEquals(List.of(), reported("""
                {
                        let q = match Int.divide(額, 10) with
                            | Int as n -> n
                            | DivisionByZero -> 0
                        硬貨枚数(q)
                    }"""));
    }

    /**
     * The control. Nothing puts the dividend at or above nought, so the quotient runs either way and
     * the construction is owed its clause — through the value case as through the operator.
     */
    @Test
    void withNothingKnownOfTheDividendBothSpellingsAreStillReported() {
        assertEquals(List.of("E2011"),
                reported("硬貨枚数(商(額 - 1000000, 10))").stream().distinct().toList());
    }
}
