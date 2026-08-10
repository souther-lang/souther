package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@code &&} and {@code ||} evaluate left to right and stop as soon as the answer is settled.
 *
 * <p>Which operands run is part of what the operators mean here rather than a choice a backend may
 * make. Souther has operations that abort — {@code /} on a zero divisor, {@code Int} overflow — so a
 * left operand is how the domain the right one is evaluated in gets narrowed, and the two strategies
 * are told apart by whether a program answers at all.
 *
 * <p>Which makes {@code x /= 0 && 100 / x > 1} the shape this is about. Evaluated eagerly it is not a
 * guard at all: the division it exists to make safe runs anyway, and the only way to write the rule
 * is an {@code if} where a condition was wanted.
 */
class AConditionStopsWhenItsAnswerIsSettledTest {

    private static final String CALC = """
            module demo
            data N = Int
            behavior calc : (n: N) -> N constructs N
            let calc (n) = N { value = %s }
            """;

    private Object run(String module, long input) throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(module), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.N", input);
        Object b = loader.loadClass("demo.Calc$Impl").getDeclaredConstructor().newInstance();
        return Codecs.encode(loader, "demo.N", Codecs.apply(b, in));
    }

    /** A false left operand settles a conjunction, so nothing on the right is evaluated. */
    @Test
    void aFalseLeftOperandSettlesAConjunction() throws Exception {
        String source = CALC.formatted("if n.value /= 0 && 100 / n.value > 1 then 1 else 0");

        assertEquals(0L, run(source, 0L));
    }

    /** A true left operand settles a disjunction. */
    @Test
    void aTrueLeftOperandSettlesADisjunction() throws Exception {
        String source = CALC.formatted("if n.value == 0 || 100 / n.value > 1 then 1 else 0");

        assertEquals(1L, run(source, 0L));
    }

    /** And where the answer is not settled, the right operand is evaluated as ever. */
    @Test
    void anUnsettledConditionStillEvaluatesTheRight() throws Exception {
        assertEquals(1L, run(CALC.formatted("if n.value /= 0 && 100 / n.value > 1 then 1 else 0"), 5L));
        assertEquals(0L, run(CALC.formatted("if n.value /= 0 && 100 / n.value > 1 then 1 else 0"), 200L));
        assertEquals(0L, run(CALC.formatted("if n.value == 0 || 100 / n.value > 1 then 1 else 0"), 200L));
        assertEquals(1L, run(CALC.formatted("if n.value == 0 || 100 / n.value > 1 then 1 else 0"), 5L));
    }
}
