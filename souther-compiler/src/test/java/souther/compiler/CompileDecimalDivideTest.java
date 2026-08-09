package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Decimal division states its rounding as a domain decision: {@code divide(a, b, scale, mode)}
 * gives a Decimal rounded to {@code scale} places by {@code mode} (spec 18.3). A zero divisor is a
 * possible input, so it returns a {@code DivisionByZero} case rather than aborting. The 2-argument
 * {@code divide} stays Int-only.
 */
class CompileDecimalDivideTest {

    // Both match cases yield Out (as the Int divide test does): match requires the branches to agree
    // on type, so the DivisionByZero case reuses p.a as a placeholder value and flags ok: false.
    private static final String MODULE = """
            module demo

            import Decimal ( divide )

            data Pair = { a: Decimal, b: Decimal }
            data Out = { value: Decimal, ok: Bool }

            behavior divv : (p: Pair) -> Out constructs Out
            let divv (p) =
                match divide(p.a, p.b, 2, HALF_UP) with
                    | Decimal as q -> Out { value = q, ok = true }
                    | DivisionByZero -> Out { value = p.a, ok = false }
            """;

    private static Object apply(BigDecimal a, BigDecimal b, BytesClassLoader loader) throws Exception {
        Object p = Codecs.decoded(loader, "demo.Pair", Map.of("a", a, "b", b));
        Object divv = loader.loadClass("demo.Divv" + "$Impl").getConstructor().newInstance();
        return Codecs.apply(divv, p);
    }

    @Test
    void dividesWithScaleAndRounding() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MODULE), CompileDecimalDivideTest.class.getClassLoader());
        // 7 / 3 = 2.333..., HALF_UP at scale 2 = 2.33
        Object out = apply(new BigDecimal("7"), new BigDecimal("3"), loader);
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(new BigDecimal("2.33"), m.get("value"));
        assertEquals(true, m.get("ok"));
    }

    @Test
    void aZeroDivisorTakesTheDivisionByZeroCase() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MODULE), CompileDecimalDivideTest.class.getClassLoader());
        Object out = apply(new BigDecimal("7"), new BigDecimal("0"), loader);
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(false, m.get("ok"));
    }

    /**
     * The two names are two declarations. Sharing one rule made them interchangeable aliases picked
     * apart by argument count, so each was reachable under the other's name — and the spec sentence
     * saying `Decimal.divide(a, b)` cannot be written was not true.
     */
    @Test
    void eachDivideTakesOnlyItsOwnArguments() {
        CompileException four = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Pair = { a: Int, b: Int }
                data Out = { n: Int }
                behavior divv : (p: Pair) -> Out constructs Out
                let divv (p) = match Int.divide(p.a, p.b, 2, HALF_UP) with
                    | Decimal as q -> Out { n = 0 }
                    | DivisionByZero -> Out { n = 0 }
                """));
        assertTrue(four.getMessage().contains("`Int.divide` takes 2"), four.getMessage());

        CompileException two = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Pair = { a: Decimal, b: Decimal }
                data Out = { n: Int }
                behavior divv : (p: Pair) -> Out constructs Out
                let divv (p) = match Decimal.divide(p.a, p.b) with
                    | Int as q -> Out { n = q }
                    | DivisionByZero -> Out { n = 0 }
                """));
        assertTrue(two.getMessage().contains("`Decimal.divide` takes 4"), two.getMessage());
    }

    @Test
    void twoArgDivideOnDecimalIsRejected() {
        String src = """
                module demo
                import Int ( divide )
                data Pair = { a: Decimal, b: Decimal }
                data Out = Decimal
                behavior divv : (p: Pair) -> Out constructs Out
                let divv (p) = Out { value = divide(p.a, p.b) }
                """;
        assertThrows(CompileException.class, () -> Compiler.compile(src));
    }

    /** A mode is a unit data, so applying one to arguments is the ordinary answer for a type
     * written where a call goes: naming it constructs it, and a construction is not a function. */
    @Test
    void aRoundingModeAppliedToArgumentsIsToldItIsNotAFunction() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data In = { n: Int }
                data Out = { n: Int }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { n = HALF_UP(i.n) }
                """));
        assertEquals("check.construct.position", e.diagnostic().messageKey());
    }
}
