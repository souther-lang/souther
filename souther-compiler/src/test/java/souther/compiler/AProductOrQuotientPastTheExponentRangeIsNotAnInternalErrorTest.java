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

    /** Two positions and a body of statements, for the shapes a rule over one position does not
     *  reach. */
    private static String overTwoPositions(String squarings, String declarations, String body) {
        return """
                module probe.follow

                %s
                data A = Decimal
                %s
                data H = { a: A, b: A }
                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (h: H) -> Verdict
                let take (h) = { %s }
                """.formatted(squarings, declarations, body);
    }

    /**
     * Each side of the comparison is a form held one by one — a coefficient at the least exponent
     * and a coefficient of one — and the difference of the two is not. The reading of the comparison
     * is what canonicalises it, so it is the reading that meets a number no ratio holds.
     */
    @Test
    void aDifferenceOfTwoFormsHeldOneByOneIsNotAnInternalError() {
        assertDoesNotThrow(() -> Compiler.compile(
                model(squarings(63), "t63 * h.a.value <= h.a.value")));
        assertDoesNotThrow(() -> Compiler.compile(
                model(squarings(63), "h.a.value <= t63 * h.a.value")));
    }

    @Test
    void theSameComparisonAsACondition() {
        assertDoesNotThrow(() -> Compiler.compile(overTwoPositions(squarings(63), "",
                "if t63 * h.a.value <= h.a.value then Ok else No")));
    }

    @Test
    void theSameComparisonAsAClauseOfADeclaration() {
        assertDoesNotThrow(() -> Compiler.compile(overTwoPositions(squarings(63),
                "    invariant tied = t63 * value <= value", "Ok")));
    }

    /** The line a rule draws is a distance between two positions, and a form over several. */
    @Test
    void everyShapeOfALineAtTheEndOfTheExponentsIsNotAnInternalError() {
        assertDoesNotThrow(() -> Compiler.compile(overTwoPositions(squarings(63), "",
                "guard h.a.value - h.b.value <= t63 else Ok\n No")));
        assertDoesNotThrow(() -> Compiler.compile(overTwoPositions(squarings(63), "",
                "guard t63 * h.a.value + h.b.value <= 1.0m else Ok\n No")));
        assertDoesNotThrow(() -> Compiler.compile(overTwoPositions(squarings(63), "",
                "guard t63 * h.a.value <= 1.0m else Ok\n guard h.b.value <= t63 else Ok\n No")));
    }

    /** Two rules on one quantity, one written at each end of the exponents: the second is read
     *  through what the first is a multiple of. */
    @Test
    void twoRulesOnOneQuantityAtBothEndsAreNotAnInternalError() {
        assertDoesNotThrow(() -> Compiler.compile(overTwoPositions(squarings(63), "",
                "guard t63 * h.a.value <= 1.0m else Ok\n guard h.a.value <= 1.0m else Ok\n No")));
        assertDoesNotThrow(() -> Compiler.compile(overTwoPositions(squarings(63), "",
                "guard h.a.value <= t63 else Ok\n guard 2.0m * h.a.value <= 1.0m else Ok\n No")));
    }
}
