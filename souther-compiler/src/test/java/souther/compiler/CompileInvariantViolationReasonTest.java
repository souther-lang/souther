package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What E2010 says a construction was refuted <em>by</em>. The check decides a violation from two
 * kinds of fact: what the values it is handed carry on their own — a literal, an arithmetic result, a
 * name given a written value, an input's own type invariant — and what a condition on the path
 * assumed. Only the second is something a guard settled, so only the second is said that way; a
 * construction refuted without any of it is said without mentioning the path at all.
 */
class CompileInvariantViolationReasonTest {

    /** The message key E2010 was raised with, which is what the reason is chosen by. */
    private static String reasonOf(String module) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(module));
        assertEquals("E2010", e.diagnostic().code(), e.getMessage());
        return e.diagnostic().messageKey();
    }

    @Test
    void aConstructionOverWrittenValuesIsRefutedWithoutAnyPath() {
        String m = """
                module demo
                data Range = { lo: Int, hi: Int }
                    invariant lo <= hi
                behavior mk : () -> Range constructs Range
                let mk = Range { lo = 5, hi = 1 }
                """;
        assertEquals("check.invariant.violation.alone", reasonOf(m),
                "nothing is guarded here — the values written decide it");
    }

    @Test
    void arithmeticOverWrittenValuesIsRefutedWithoutAnyPath() {
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                behavior calc : (m: Money) -> Money constructs Money
                let calc (m) = Money(0m) - Money(1m)
                """;
        assertEquals("check.invariant.violation.alone", reasonOf(m),
                "0 - 1 is negative wherever it stands");
    }

    @Test
    void anInputsOwnInvariantRefutesWithoutAnyPath() {
        // `p.value > 0` is what Pos guarantees of its value, not what a guard settled
        String m = """
                module demo
                data Pos = Int
                    invariant value > 0
                data Neg = Int
                    invariant value < 0
                behavior conv : (p: Pos) -> Neg constructs Neg
                let conv (p) = Neg(p.value)
                """;
        assertEquals("check.invariant.violation.alone", reasonOf(m),
                "an input's type carries its invariant everywhere the input does");
    }

    @Test
    void aNameGivenAWrittenValueIsRefutedWithoutAnyPath() {
        String m = """
                module demo
                data Amount = Int
                    invariant value >= 0
                behavior mk : (n: Int) -> Amount constructs Amount
                let mk (n) = {
                    let bad = 0 - 5
                    Amount(bad)
                }
                """;
        assertEquals("check.invariant.violation.alone", reasonOf(m),
                "a name is an alias for what it was given, and no guard was written");
    }

    @Test
    void aGuardThatForcesTheViolationIsSaidAsAnAssumption() {
        String m = """
                module demo
                data Amount = Int
                    invariant value >= 0
                behavior mk : (n: Int) -> Amount constructs Amount
                let mk (n) =
                    if n < 0 then Amount(n)
                    else Amount(0)
                """;
        assertEquals("check.invariant.violation.assumed", reasonOf(m),
                "without `n < 0` nothing here refutes the invariant");
    }

    @Test
    void aGuardBesideAViolationIsNotItsReason() {
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Pair = { a: Money, b: Money }
                behavior pick : (p: Pair) -> Money constructs Money
                let pick (p) =
                    if p.a < p.b then Money(0m) - Money(1m)
                    else p.a
                """;
        assertEquals("check.invariant.violation.alone", reasonOf(m),
                "the guard settles something, and the violation does not need it");
    }

    @Test
    void twoReadingsRefutedDifferentlyStayAnErrorAndAreSaidAsTheWeakerOne() {
        // read with `n`, the guard decides it; read with `0 - 1`, the value does. Either way the
        // construction violates, so it stays an error — and what is claimed of the two together is
        // what the reading that needed the path supports.
        String m = """
                module demo
                data Amount = Int
                    invariant value >= 0
                behavior mk : (n: Int) -> Amount constructs Amount
                let mk (n) = Amount(if n < 0 then n else 0 - 1)
                """;
        assertEquals("check.invariant.violation.assumed", reasonOf(m),
                "one reading needed the path, so the two together are said to");
    }
}
