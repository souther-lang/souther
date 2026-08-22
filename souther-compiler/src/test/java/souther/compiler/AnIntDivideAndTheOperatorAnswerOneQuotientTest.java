package souther.compiler;

import souther.runtime.ConstraintViolation;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * {@code Int.divide(a, b)} and {@code a / b} are one division, and they part company over a zero
 * divisor and nowhere else.
 *
 * <p>Which is what §stdlib-int states: the operator is the casual one and aborts, the function
 * answers the zero divisor as a case, and both are truncating division of the same two numbers.
 * The invariant-discharge check reads the value case of {@code Int.divide} as the quotient the
 * operator answers, so a pair where the two produce different numbers is a pair where that reading
 * is wrong.
 *
 * <p>{@code Long.MIN_VALUE / -1} is the pair. Its quotient is one past what an {@code Int} holds,
 * so §stdlib-int aborts on it as it does on any other overflow — and a raw {@code ldiv} wraps it
 * back to {@code Long.MIN_VALUE} instead, which is what stood in the function's success path.
 */
class AnIntDivideAndTheOperatorAnswerOneQuotientTest {

    private static final String MODULE = """
            module demo

            import Int ( divide )

            data Pair = { a: Int, b: Int }
            data Outcome = { q: Int, ok: Bool }

            behavior byTheFunction : (p: Pair) -> Outcome constructs Outcome
            let byTheFunction (p) =
                match divide(p.a, p.b) with
                    | Int as q -> Outcome { q = q, ok = true }
                    | DivisionByZero -> Outcome { q = 0, ok = false }

            behavior byTheOperator : (p: Pair) -> Outcome constructs Outcome
            let byTheOperator (p) = Outcome { q = p.a / p.b, ok = true }
            """;

    private final BytesClassLoader loader =
            new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());

    private Map<?, ?> answered(String behavior, long a, long b) throws Exception {
        Object pair = Codecs.decoded(loader, "demo.Pair", Map.of("a", a, "b", b));
        Object outcome = Codecs.apply(
                Emitted.behavior(loader, "demo", behavior).getConstructor().newInstance(), pair);
        return (Map<?, ?>) Codecs.encode(loader, "demo.Outcome", outcome);
    }

    @Test
    void bothAnswerTheSameQuotientWhereTheOperatorAnswersOne() throws Exception {
        assertEquals(answered("byTheOperator", -7, 2).get("q"),
                answered("byTheFunction", -7, 2).get("q"),
                "truncating toward zero, so -7 / 2 is -3 by either spelling");
    }

    @Test
    void bothAbortOnTheOnePairNoIntHoldsTheQuotientOf() {
        assertThrows(ConstraintViolation.class,
                () -> answered("byTheOperator", Long.MIN_VALUE, -1));
        assertThrows(ConstraintViolation.class,
                () -> answered("byTheFunction", Long.MIN_VALUE, -1),
                "the function answers a case for a zero divisor, not for an overflow");
    }

    @Test
    void onlyTheFunctionAnswersAZeroDivisor() throws Exception {
        Map<?, ?> out = answered("byTheFunction", 10, 0);
        assertEquals(false, out.get("ok"));
        assertThrows(ConstraintViolation.class, () -> answered("byTheOperator", 10, 0));
    }
}
