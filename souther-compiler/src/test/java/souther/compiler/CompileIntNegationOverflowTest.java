package souther.compiler;

import souther.runtime.ConstraintViolation;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Unary minus on {@code Int} is {@code 0 - n}: the smallest {@code Int} has no positive counterpart,
 * so negating it overflows the same way {@code Int.MIN - 1} does, and aborts rather than wraps (spec
 * §stdlib-int, which states this explicitly for {@code abs}). {@code Decimal} and {@code Rational}
 * negation only flip a sign and stay total (issue #1878).
 */
class CompileIntNegationOverflowTest {

    private static String intModule(String bodyExpr) {
        return """
                module demo

                data In = Int
                data Out = Int

                behavior compute : (x: In) -> Out constructs Out

                let compute (x) = Out { value = %s }
                """.formatted(bodyExpr);
    }

    private static Object runInt(String bodyExpr, long input) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(intModule(bodyExpr)),
                CompileIntNegationOverflowTest.class.getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", input);
        Object compute = Emitted.behavior(loader, "demo", "compute").getConstructor().newInstance();
        Object out = Codecs.apply(compute, in);
        return Codecs.encode(loader, "demo.Out", out);
    }

    @Test
    void negatingTheSmallestIntAborts() {
        assertThrows(ConstraintViolation.class, () -> runInt("-x.value", Long.MIN_VALUE));
    }

    @Test
    void negatingAnOrdinaryIntIsUnaffected() throws Exception {
        assertEquals(-100L, runInt("-x.value", 100L));
        assertEquals(Long.MIN_VALUE + 1, runInt("-x.value", Long.MAX_VALUE));
    }

    @Test
    void negatingADecimalStaysTotal() throws Exception {
        String module = """
                module demo

                data In = Decimal
                data Out = Decimal

                behavior compute : (x: In) -> Out constructs Out

                let compute (x) = Out { value = -x.value }
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(module), getClass().getClassLoader());
        BigDecimal huge = new BigDecimal(BigDecimal.ONE.unscaledValue(), Integer.MIN_VALUE + 1);
        Object in = Codecs.decoded(loader, "demo.In", huge);
        Object compute = Emitted.behavior(loader, "demo", "compute").getConstructor().newInstance();
        Object out = Codecs.apply(compute, in);
        assertEquals(huge.negate(), Codecs.encode(loader, "demo.Out", out));
    }
}
