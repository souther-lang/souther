package souther.compiler;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rounding mode is an ordinary value of the {@code RoundingMode} data declared by core: it is
 * evaluated at the call like any other argument, so a model can state a policy once and pass it,
 * choose one from a business rule, or hand an operation taking one to a combinator. Each of the
 * three Decimal operations takes its mode through a different route here, so all three are ordinary
 * functions rather than special forms.
 */
class CompileRoundingModeValueTest {

    private static Map<?, ?> run(String source, Map<String, Object> in) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source),
                CompileRoundingModeValueTest.class.getClassLoader());
        Object behavior = Emitted.behavior(loader, "demo", "go").getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", in)));
    }

    /** The mode reaches {@code divide} through a binding rather than being written at the call. */
    @Test
    void divideTakesAModeBoundToAName() throws Exception {
        String src = """
                module demo

                import Decimal ( divide )

                data In = { a: Decimal, b: Decimal }
                data Out = { value: Decimal, ok: Bool }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let mode = HALF_UP
                    match divide(i.a, i.b, 2, mode) with
                        | Decimal as q -> Out { value = q, ok = true }
                        | DivisionByZero -> Out { value = i.a, ok = false }
                }
                """;
        Map<?, ?> out = run(src,
                Map.of("a", new BigDecimal("7"), "b", new BigDecimal("3")));
        assertEquals(new BigDecimal("2.33"), out.get("value"));
        assertEquals(true, out.get("ok"));
    }

    /** The mode reaches {@code round} as the value an {@code if} chose at run time. */
    @Test
    void roundTakesAModeChosenByAnIf() throws Exception {
        String src = """
                module demo

                data In = { d: Decimal, up: Bool }
                data Out = { r: Decimal }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { r = Decimal.round(1, if i.up then CEILING else FLOOR, i.d) }
                """;
        assertEquals(new BigDecimal("86.5"),
                run(src, Map.of("d", new BigDecimal("86.41"), "up", true)).get("r"));
        assertEquals(new BigDecimal("86.4"),
                run(src, Map.of("d", new BigDecimal("86.49"), "up", false)).get("r"));
    }

    /** {@code toInt} is handed over by name and applied through the binding. */
    @Test
    void toIntIsHandedOverAndAppliedThroughABinding() throws Exception {
        String src = """
                module demo

                data In = { d: Decimal }
                data Out = { n: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let convert = Decimal.toInt
                    Out { n = convert(HALF_UP, i.d) }
                }
                """;
        assertEquals(87L, run(src, Map.of("d", new BigDecimal("86.5"))).get("n"));
    }

    /** A mode is a value of a type a binding can be annotated with. */
    @Test
    void aModeIsAValueOfTheRoundingModeType() throws Exception {
        String src = """
                module demo

                data In = { d: Decimal }
                data Out = { n: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let mode: RoundingMode = FLOOR
                    Out { n = Decimal.toInt(mode, i.d) }
                }
                """;
        assertEquals(86L, run(src, Map.of("d", new BigDecimal("86.9"))).get("n"));
    }

    /** The mode is the result of an ordinary helper call, evaluated like any other argument. */
    @Test
    void aHelperComputesTheModeAtTheCall() throws Exception {
        String src = """
                module demo

                data In = { d: Decimal, up: Bool }
                data Out = { n: Int }

                behavior go : (i: In) -> Out constructs Out

                let pick (up: Bool): RoundingMode = if up then CEILING else FLOOR

                let go (i) = Out { n = Decimal.toInt(pick(i.up), i.d) }
                """;
        assertEquals(87L, run(src, Map.of("d", new BigDecimal("86.1"), "up", true)).get("n"));
        assertEquals(86L, run(src, Map.of("d", new BigDecimal("86.9"), "up", false)).get("n"));
    }
}
