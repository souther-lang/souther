package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

/**
 * A decimal squared again and again has an exponent that doubles each time, and the least exponent a
 * ratio holds is reached after sixty-three squarings of a tenth. A product or a quotient of such
 * constants is a value the exact arithmetic has no representation for, and the analysis meets it while
 * reading the model's own numbers. What it says about such a program is up to the phase that meets it;
 * that it says something and does not stop with an internal error is what every phase owes.
 */
class AProductOrQuotientPastTheExponentRangeIsNotAnInternalErrorTest {

    private static String squarings(int upTo) {
        StringBuilder chain = new StringBuilder("let sq (x: Decimal): Decimal = x * x\n\nlet t0 = 0.1m\n");
        for (int i = 1; i <= upTo; i++) {
            chain.append("let t").append(i).append(" = sq(t").append(i - 1).append(")\n");
        }
        return chain.toString();
    }

    private static String model(String squarings, String guard) {
        return """
                module probe.follow

                %s
                data A = Decimal
                data H = { a: A }
                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (h: H) -> Verdict
                let take (h) = { guard %s else Ok
                    No }
                """.formatted(squarings, guard);
    }

    @Test
    void aBoundThatIsTheSquareOfTheLeastExponentIsNotAnInternalError() {
        assertDoesNotThrow(() -> Compiler.compile(model(squarings(64), "h.a.value <= t64")));
    }

    @Test
    void aCoefficientAtTheLeastExponentIsNotAnInternalError() {
        assertDoesNotThrow(() -> Compiler.compile(model(squarings(63), "t63 * h.a.value <= 1.0m")));
    }

    @Test
    void aCoefficientPastTheLeastExponentIsNotAnInternalError() {
        assertDoesNotThrow(() -> Compiler.compile(model(squarings(64), "t64 * h.a.value <= 1.0m")));
    }
}
