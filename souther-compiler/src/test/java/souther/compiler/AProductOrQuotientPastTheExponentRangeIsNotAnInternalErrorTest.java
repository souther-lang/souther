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

    /**
     * Every shape a rule at the end of the exponents takes, each a behavior of its own over values
     * no other behavior's rules are about, compiled together: a phase meets each where it reads that
     * behavior, and an internal error at any of them stops the compile.
     *
     * <ul>
     *   <li>a bound that is the square of the least exponent, and a coefficient at it and past it;
     *   <li>a comparison whose two sides are each a form held one by one — a coefficient at the
     *       least exponent and a coefficient of one — while their difference is not, so it is the
     *       reading of the comparison that meets a number no ratio holds; written either way round,
     *       as a condition, and as a clause of a declaration, on a type only that behavior takes;
     *   <li>a line that is a distance between two positions, and a form over several;
     *   <li>two rules on one quantity, one written at each end of the exponents, the second read
     *       through what the first is a multiple of.
     * </ul>
     */
    @Test
    void everyShapeOfARuleAtTheEndOfTheExponentsIsNotAnInternalError() {
        String source = """
                module probe.follow

                %s
                data A = Decimal
                data Tied = Decimal
                    invariant tied = t63 * value <= value
                data H = { a: A, b: A }
                data HeldTied = { a: Tied, b: Tied }
                data Ok
                data No
                data Verdict = Ok | No

                behavior squareOfTheLeast : (h: H) -> Verdict
                let squareOfTheLeast (h) = { guard h.a.value <= t64 else Ok
                    No }
                behavior atTheLeast : (h: H) -> Verdict
                let atTheLeast (h) = { guard t63 * h.a.value <= 1.0m else Ok
                    No }
                behavior pastTheLeast : (h: H) -> Verdict
                let pastTheLeast (h) = { guard t64 * h.a.value <= 1.0m else Ok
                    No }
                behavior aDifference : (h: H) -> Verdict
                let aDifference (h) = { guard t63 * h.a.value <= h.a.value else Ok
                    No }
                behavior theOtherWayRound : (h: H) -> Verdict
                let theOtherWayRound (h) = { guard h.a.value <= t63 * h.a.value else Ok
                    No }
                behavior asACondition : (h: H) -> Verdict
                let asACondition (h) = { if t63 * h.a.value <= h.a.value then Ok else No }
                behavior asAClause : (h: HeldTied) -> Verdict
                let asAClause (h) = { Ok }
                behavior aDistance : (h: H) -> Verdict
                let aDistance (h) = { guard h.a.value - h.b.value <= t63 else Ok
                    No }
                behavior overSeveral : (h: H) -> Verdict
                let overSeveral (h) = { guard t63 * h.a.value + h.b.value <= 1.0m else Ok
                    No }
                behavior oneOfEach : (h: H) -> Verdict
                let oneOfEach (h) = { guard t63 * h.a.value <= 1.0m else Ok
                    guard h.b.value <= t63 else Ok
                    No }
                behavior bothEndsAfterTheLeast : (h: H) -> Verdict
                let bothEndsAfterTheLeast (h) = { guard t63 * h.a.value <= 1.0m else Ok
                    guard h.a.value <= 1.0m else Ok
                    No }
                behavior bothEndsAfterAMultiple : (h: H) -> Verdict
                let bothEndsAfterAMultiple (h) = { guard h.a.value <= t63 else Ok
                    guard 2.0m * h.a.value <= 1.0m else Ok
                    No }
                """.formatted(squarings(64));

        assertDoesNotThrow(() -> Compiler.compile(source));
    }
}
