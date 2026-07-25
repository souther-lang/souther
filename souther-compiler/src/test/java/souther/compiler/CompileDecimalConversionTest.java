package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Int and Decimal meet only where the conversion is written. An arithmetic operator takes two
 * operands of one type (as F#'s does — `n * 0.1m` does not compile there either), so a rate applied
 * to an amount reads `Decimal.fromInt(amount) * rate`. The widening is exact and needs nothing
 * stated; the narrowing drops a fraction, so `Decimal.toInt(d, mode)` says which way it goes.
 */
class CompileDecimalConversionTest {

    private static final String MODULE = """
            module demo

            data In = { 税抜: Int, 税率: Decimal }
            data Out = { 切捨: Int, 四捨五入: Int, 切上: Int, 税額: Decimal }

            behavior run : (i: In) -> Out constructs Out

            let 税額 (i: In): Decimal = Decimal.fromInt(i.税抜) * i.税率

            let run (i) = Out {
                切捨 = Decimal.toInt(税額(i), FLOOR),
                四捨五入 = Decimal.toInt(税額(i), HALF_UP),
                切上 = Decimal.toInt(税額(i), CEILING),
                税額 = 税額(i)
            }
            """;

    private Map<?, ?> run(long 税抜, String 税率) throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("税抜", 税抜, "税率", new BigDecimal(税率)));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
    }

    @Test
    void aRateAppliedToAnAmountRoundsTheWayTheCallSays() throws Exception {
        // 1080 * 0.08 = 86.40 — the three modes disagree, which is the point of writing one.
        Map<?, ?> m = run(1080L, "0.08");
        assertEquals(new BigDecimal("86.40"), m.get("税額"));
        assertEquals(86L, m.get("切捨"));
        assertEquals(86L, m.get("四捨五入"));
        assertEquals(87L, m.get("切上"));
    }

    @Test
    void halfUpRoundsAwayFromZeroAtTheHalf() throws Exception {
        // 1005 * 0.10 = 100.50
        Map<?, ?> m = run(1005L, "0.10");
        assertEquals(100L, m.get("切捨"));
        assertEquals(101L, m.get("四捨五入"));
    }

    @Test
    void mixingIntAndDecimalInOneOperatorIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { 税抜: Int, 税率: Decimal }
                data Out = { v: Decimal }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { v = i.税抜 * i.税率 }
                """));
        assertTrue(e.getMessage().contains("INT") && e.getMessage().contains("DECIMAL"),
                e.getMessage());
    }

    @Test
    void theRoundingModeIsNotOptional() {
        assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { d: Decimal }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { n = Decimal.toInt(i.d) }
                """));
    }
}
