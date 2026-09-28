package souther.compiler;

import souther.compiler.diag.CompileException;

import souther.runtime.ConstraintViolation;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Closed newtype arithmetic (spec §newtype-arithmetic): {@code +}/{@code -} over a single-value
 * numeric newtype yield that newtype. The base op runs on the wrapped value and the result is
 * re-wrapped, re-checking the newtype's invariant at construction — so a subtraction that leaves the
 * invariant aborts, exactly as any other construction would. {@code *} stays rejected, and so do two
 * different newtypes.
 *
 * <p>{@code /} is not among the closed ones. A newtype over a newtype's own units is the number its
 * units leave, so dividing one by another of the same type answers a {@code Rational} and not the
 * newtype — the operator that does not stay inside the wrapper is refused only where the two types
 * differ, which is a dimension it would have had to invent.
 */
class CompileClosedNewtypeArithmeticTest {

    private Object run(String module, String type, Object input) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo." + type, input);
        Object b = Emitted.behavior(loader, "demo", "calc").getDeclaredConstructor().newInstance();
        Object out = Codecs.apply(b, in);
        return Codecs.encode(loader, "demo." + type, out);
    }

    // Closed arithmetic re-wraps an existing value's result — like Int arithmetic, it is a
    // computation, not a fresh mint from raw data, so it needs no `constructs` (a `NewData` literal
    // such as `Money(10m)` still does; see subtractionThatBreaksTheInvariant... below).

    @Test
    void intNewtypeAddsAndStaysTheNewtype() throws Exception {
        String m = """
                module demo
                data N = Int
                behavior calc : (n: N) -> N
                let calc (n) = n + n
                """;
        assertEquals(14L, run(m, "N", 7L));
    }

    @Test
    void decimalNewtypeSubtracts() throws Exception {
        String m = """
                module demo
                data Money = Decimal
                behavior calc : (m: Money) -> Money
                let calc (m) = m - m
                """;
        assertEquals(0, ((BigDecimal) run(m, "Money", new BigDecimal("5"))).compareTo(BigDecimal.ZERO));
    }

    @Test
    void aNewtypeLiteralOperandIsTakenAsTheNewtype() throws Exception {
        // `n + 3` — the bare literal is taken as N, the result is N (spec §newtype-comparison rule)
        String m = """
                module demo
                data N = Int
                behavior calc : (n: N) -> N
                let calc (n) = n + 3
                """;
        assertEquals(10L, run(m, "N", 7L));
    }

    @Test
    void subtractionThatBreaksTheInvariantAbortsAtTheReWrap() {
        // Money is non-negative; `m - Money(10)` goes negative for a small m and aborts on the
        // re-wrap's invariant check — closed arithmetic re-checks the invariant like any construction.
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                behavior calc : (m: Money) -> Money constructs Money
                let calc (m) = m - Money(10m)
                """;
        assertThrows(ConstraintViolation.class, () -> run(m, "Money", new BigDecimal("5")));
    }

    @Test
    void scalarMultiplyStaysTheNewtype() throws Exception {
        // `n * 2` scales a newtype by a plain scalar and stays the newtype (dimension unchanged)
        String m = """
                module demo
                data N = Int
                behavior calc : (n: N) -> N
                let calc (n) = n * 2
                """;
        assertEquals(14L, run(m, "N", 7L));
    }

    @Test
    void scalarOnTheLeft() throws Exception {
        assertEquals(14L, run("""
                module demo
                data N = Int
                behavior calc : (n: N) -> N
                let calc (n) = 2 * n
                """, "N", 7L));
    }

    /**
     * And a newtype is not divided by a value of its base: the dimension survives, the quotient is
     * exact, and no {@code N} holds one (spec §newtype-arithmetic). What a model writes instead is the
     * quantisation it means, on the value.
     */
    @Test
    void scalarDivisionIsNotInherited() throws Exception {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data N = Int
                behavior calc : (n: N) -> N
                let calc (n) = n / 2
                """));
        assertTrue(refused.getMessage().contains("no Int is left to wrap as N"),
                refused.getMessage());
        assertEquals(3L, run("""
                module demo
                data N = Int
                behavior calc : (n: N) -> N
                let calc (n) = N(Rational.toInt(DOWN, n.value / 2))
                """, "N", 7L));
    }

    @Test
    void scalarDividedByANewtypeIsRejected() {
        // `2 / n` is an inverse (money⁻¹), a dimension change — division is not commutative, so a
        // scalar on the left is rejected (only `n / 2` scales)
        String m = """
                module demo
                data N = Int
                behavior calc : (n: N) -> N
                let calc (n) = 2 / n
                """;
        assertThrows(CompileException.class, () -> Compiler.compile(m));
    }

    @Test
    void newtypeTimesNewtypeIsRejected() {
        // a product of two newtypes would change dimension (units), which is not modeled
        String m = """
                module demo
                data Money = Int
                data Qty = Int
                data P = { m: Money, q: Qty }
                behavior calc : (p: P) -> Money
                let calc (p) = p.m * p.q
                """;
        assertThrows(CompileException.class, () -> Compiler.compile(m));
    }

    @Test
    void twoDifferentNewtypesDoNotCombine() {
        String m = """
                module demo
                data Money = Int
                data Qty = Int
                data P = { m: Money, q: Qty }
                behavior calc : (p: P) -> Money constructs Money
                let calc (p) = p.m + p.q
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(m));
        assertTrue(e.getMessage().contains("Money") || e.getMessage().contains("arithmetic"),
                "different newtypes must not combine: " + e.getMessage());
    }

    @Test
    void multiplyOnANewtypeStaysRejected() {
        // `newtype * newtype` changes dimension (money squared), so it is rejected — only scalar
        // multiply by a plain number stays in the newtype (spec §newtype-arithmetic)
        String m = """
                module demo
                data Money = Int
                behavior calc : (n: Money) -> Money constructs Money
                let calc (n) = n * n
                """;
        assertThrows(CompileException.class, () -> Compiler.compile(m));
    }
}
