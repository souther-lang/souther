package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An exact quotient by a value, narrowed to a whole number, lies between the whole numbers either
 * side of the quotients at the corners of what its dividend and divisor lie between.
 *
 * <p>{@code /} answers a Rational, and no construction holds one, so the quotient is no term of its
 * own. {@code Rational.toInt} narrows it to an {@code Int}, and every mode lands it on one of the two
 * whole numbers the exact quotient lies between — a quotient rounded to the scale nought
 * (spec §invariant-discharge-arithmetic). Where the path holds the divisor off nought, what holds of
 * the dividend and the divisor is what holds of the narrowed answer, and a guard restating it is one
 * the model need not write.
 */
class ANarrowedQuotientByAValueLiesBetweenItsCornersTest {

    private static String model(String bounds, String body) {
        return """
                module demo

                data Share = Int
                    invariant %s

                behavior apportion : (amount: Int, among: Int) -> Share
                    constructs Share

                let apportion (amount, among) = {
                    %s
                }
                """.formatted(bounds, body);
    }

    private static List<String> reported(String bounds, String body) {
        return Compiler.compileWithWarnings(model(bounds, body)).warnings().stream()
                .map(Diagnostic::code)
                .toList();
    }

    /**
     * An amount at or above nought shared among a count above nought narrows to a share at or above
     * nought, and nothing restates it: no guard is owed, and none written would be a branch nothing
     * reaches.
     */
    @Test
    void aShareOfANonNegativeAmountAmongAPositiveCountIsNotNegative() {
        assertEquals(List.of(), reported("value >= 0", """
                guard amount >= 0 else Share(1)
                    guard among >= 1 else Share(1)
                    Share(Rational.toInt(DOWN, amount / among))"""));
    }

    /**
     * By a constant the quotient is arithmetic over the dividend, and the narrowing is within one of
     * it whichever mode it is handed (spec §invariant-discharge-guarantees).
     */
    @Test
    void aShareByAConstantIsWithinOneOfTheQuotient() {
        assertEquals(List.of(), reported("value >= 0", """
                guard amount >= 0 else Share(1)
                    Share(Rational.toInt(DOWN, amount / 2))"""));
    }

    /**
     * And a narrowing of arithmetic over a quotient by a constant, which is no quotient and has no
     * corners: what is known of it is that it is within one of what it rounds.
     */
    @Test
    void aNarrowingOfArithmeticOverAQuotientIsWithinOneOfIt() {
        assertEquals(List.of(), reported("value >= 0", """
                guard amount >= 0 else Share(1)
                    Share(Rational.toInt(DOWN, amount / 2 + 1))"""));
    }

    /** Every mode lands on one of the two whole numbers, so none of them is read. */
    @Test
    void theModeIsNotRead() {
        for (String mode : List.of("UP", "CEILING", "FLOOR", "HALF_UP", "HALF_EVEN", "HALF_DOWN")) {
            assertEquals(List.of(), reported("value >= 0", """
                    guard amount >= 0 else Share(1)
                        guard among >= 1 else Share(1)
                        Share(Rational.toInt(%s, amount / among))""".formatted(mode)), mode);
        }
    }

    /** The quotient given a name first is the quotient. */
    @Test
    void aQuotientGivenANameIsTheQuotient() {
        assertEquals(List.of(), reported("value >= 0", """
                guard amount >= 0 else Share(1)
                    guard among >= 1 else Share(1)
                    let q = amount / among
                    Share(Rational.toInt(DOWN, q))"""));
    }

    /** A quotient whose dividend is a name bound inside the value the quotient was given is the
     * quotient of what that name was given. */
    @Test
    void aQuotientIsReadWhereItsOperandsWereNamed() {
        assertEquals(List.of(), reported("value >= 0", """
                guard amount >= 0 else Share(1)
                    guard among >= 1 else Share(1)
                    let q = {
                        let held = amount * 2
                        held / among
                    }
                    Share(Rational.toInt(DOWN, q))"""));
    }

    /**
     * The control. A divisor that may be on either side of nought is no divisor the rule reads, and
     * the share is not taken to be at or above nought for want of a sign.
     */
    @Test
    void aDivisorOfEitherSignStatesNothing() {
        assertEquals(List.of("E2011"), reported("value >= 0", """
                guard amount >= 0 else Share(1)
                    guard among /= 0 else Share(1)
                    Share(Rational.toInt(DOWN, amount / among))"""));
    }

    /**
     * A quotient no decimal writes is held outward at each end: a third lies between nought and
     * one, so a share of one among three is at most one and at least nought, and not more than
     * that.
     */
    @Test
    void aQuotientNoDecimalWritesIsHeldOutward() {
        String oneAmongThree = """
                guard amount == 1 else Share(1)
                    guard among == 3 else Share(1)
                    Share(Rational.toInt(CEILING, amount / among))""";
        assertEquals(List.of(), reported("value >= 0 && value <= 1", oneAmongThree));
        assertEquals(List.of("E2011"), reported("value >= 1", oneAmongThree),
                "the mode is not read, so the share is not shown to be one rather than nought");
    }

    /**
     * A divisor held at nought leaves no answer: the divide aborts, nothing after it is reached,
     * and the construction there is not judged rather than judged against a range of nothing.
     */
    @Test
    void aDivisorHeldAtNoughtLeavesNothingToJudge() {
        assertEquals(List.of(), reported("value >= 0", """
                guard among == 0 else Share(1)
                    Share(Rational.toInt(DOWN, (0 - 5) / among))"""));
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileWithWarnings(model("value >= 0", """
                        guard among == 1 else Share(1)
                            Share(Rational.toInt(DOWN, (0 - 5) / among))""")),
                "the same construction past a divisor of one is reached, and refused");
        assertEquals("E2010", refused.getMessage().substring(0, 5), refused.getMessage());
    }
}
