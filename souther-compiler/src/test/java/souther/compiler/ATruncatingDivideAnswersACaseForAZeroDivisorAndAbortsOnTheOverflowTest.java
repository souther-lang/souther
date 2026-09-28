package souther.compiler;

import souther.runtime.ConstraintViolation;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * {@code Int.truncatingDivide} has two ways of not answering a quotient, and they are not one.
 *
 * <p>A zero divisor is a possible input on the business flow, so it comes back as a case. An overflow
 * is a model bug, so it aborts — and there is one pair it happens to: the quotient of
 * {@code Long.MIN_VALUE} by {@code -1} is one past what an {@code Int} holds. A raw {@code ldiv}
 * wraps that back to {@code Long.MIN_VALUE} and answers it as a quotient, which is what stood in the
 * value path (spec §stdlib-int).
 *
 * <p>The remainder is the companion and answers on that very pair, which is why it stays a raw
 * {@code lrem}.
 */
class ATruncatingDivideAnswersACaseForAZeroDivisorAndAbortsOnTheOverflowTest {

    private static final String MODULE = """
            module demo

            import Int ( truncatingDivide )

            data Pair = { a: Int, b: Int }
            data Outcome = { q: Int, ok: Bool }

            behavior byTheFunction : (p: Pair) -> Outcome constructs Outcome
            let byTheFunction (p) =
                match truncatingDivide(p.a, p.b) with
                    | Int as q -> Outcome { q = q, ok = true }
                    | DivisionByZero -> Outcome { q = 0, ok = false }

            behavior whatIsLeft : (p: Pair) -> Outcome constructs Outcome
            let whatIsLeft (p) =
                match Int.truncatingRemainder(p.a, p.b) with
                    | Int as r -> Outcome { q = r, ok = true }
                    | DivisionByZero -> Outcome { q = 0, ok = false }
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
    void theQuotientIsTruncatedTowardNought() throws Exception {
        assertEquals(-3L, answered("byTheFunction", -7, 2).get("q"));
        assertEquals(3L, answered("byTheFunction", 7, 2).get("q"));
    }

    @Test
    void itAbortsOnTheOnePairNoIntHoldsTheQuotientOf() {
        assertThrows(ConstraintViolation.class,
                () -> answered("byTheFunction", Long.MIN_VALUE, -1),
                "the case is for a zero divisor, not for an overflow");
    }

    /**
     * The remainder answers on the pair the quotient aborts on, and answers nought.
     *
     * <p>Which is why it stays a raw {@code lrem}: what is left is exact for every pair — the
     * quotient of {@code Long.MIN_VALUE} by {@code -1} is one past what an {@code Int} holds, and
     * what it leaves is nothing at all. A remainder held to the quotient's abort would refuse a pair
     * it answers for.
     */
    @Test
    void theRemainderAnswersOnThePairTheQuotientAbortsOn() throws Exception {
        Map<?, ?> out = answered("whatIsLeft", Long.MIN_VALUE, -1);
        assertEquals(0L, out.get("q"));
        assertEquals(true, out.get("ok"));
    }

    @Test
    void aZeroDivisorComesBackAsACase() throws Exception {
        Map<?, ?> out = answered("byTheFunction", 10, 0);
        assertEquals(false, out.get("ok"));
        assertEquals(0L, out.get("q"));
    }
}
