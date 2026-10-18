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
 * the model need not write. A whole divisor the path leaves on both sides of nought is read on each.
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
     * A whole divisor that may be on either side of nought divides by at least one either way, so
     * the share lies within the span of the shares by each side: a hundred among one, and a hundred
     * among minus one. Not nearer than that, and not on one side of nought for want of a sign.
     *
     * <p>Each claim left owed has a share that breaks it, and the share is checked rather than
     * named: pinned to those inputs the reading is exact, and the construction is refused.
     */
    @Test
    void aWholeDivisorOfEitherSignBoundsTheShareByEachSide() {
        String amongAny = """
                guard amount >= 0 && amount <= 100 else Share(1)
                    guard among /= 0 else Share(1)
                    Share(Rational.toInt(DOWN, amount / among))""";
        assertEquals(List.of(), reported("value >= 0 - 100 && value <= 100", amongAny));
        assertEquals(List.of("E2011"), reported("value <= 99", amongAny));
        refusedAt("value <= 99", 100, "1");
        assertEquals(List.of("E2011"), reported("value >= 0 - 99", amongAny));
        refusedAt("value >= 0 - 99", 100, "0 - 1");
        assertEquals(List.of("E2011"), reported("value >= 0", amongAny));
        refusedAt("value >= 0", 1, "0 - 1");
    }

    /** And without a guard on the divisor: a divide by nought answers nothing, so what is judged is
     * the share by the divisor's other values. */
    @Test
    void aWholeDivisorNoughtIsAmongBoundsTheShareByTheOthers() {
        assertEquals(List.of(), reported("value >= 0 - 100 && value <= 100", """
                guard amount >= 0 && amount <= 100 else Share(1)
                    Share(Rational.toInt(DOWN, amount / among))"""));
    }

    /**
     * The control beside the whole divisors: a decimal divisor that may be nought is read on
     * neither side, since a decimal other than nought can be nearer nought than any number named.
     * Under {@code y > 0}, a divisor of {@code y - 1} is minus a half at a half, and one shared that
     * way is minus two, which the claim fails.
     */
    @Test
    void aDecimalDivisorThatMayBeNoughtStatesNothing() {
        String model = """
                module demo

                data Share = Int
                    invariant value >= 0

                behavior apportion : (amount: Decimal, y: Decimal) -> Share
                    constructs Share

                let apportion (amount, y) = {
                    guard amount >= 0m && amount <= 100m else Share(1)
                    guard y > 0m else Share(1)
                    Share(Rational.toInt(DOWN, amount / (y - 1m)))
                }
                """;
        assertEquals(List.of("E2011"), Compiler.compileWithWarnings(model).warnings().stream()
                .map(Diagnostic::code).toList());
    }

    /** A dividend of either sign by a divisor of either sign: the span is the dividend's furthest
     * end either way, which a divide by one or by minus one reaches. */
    @Test
    void aDividendAndADivisorBothEitherSideOfNoughtSpanTheDividendEitherWay() {
        String both = """
                guard amount >= 0 - 100 && amount <= 100 else Share(1)
                    guard among >= 0 - 5 && among <= 5 else Share(1)
                    Share(Rational.toInt(DOWN, amount / among))""";
        assertEquals(List.of(), reported("value >= 0 - 100 && value <= 100", both));
        assertEquals(List.of("E2011"), reported("value >= 0 - 99", both));
        refusedAt("value >= 0 - 99", 100, "0 - 1");
    }

    /**
     * A divisor nought is the one end of is read on its other side alone, so the share keeps the
     * dividend's sign there, as it does by a divisor held off nought. The span of both sides would
     * have lost it.
     */
    @Test
    void aWholeDivisorNoughtEndsIsReadOnItsOtherSide() {
        assertEquals(List.of(), reported("value >= 0 && value <= 100", """
                guard amount >= 0 && amount <= 100 else Share(1)
                    guard among >= 0 && among <= 5 else Share(1)
                    Share(Rational.toInt(DOWN, amount / among))"""));
        assertEquals(List.of(), reported("value >= 0 - 100 && value <= 0", """
                guard amount >= 0 && amount <= 100 else Share(0)
                    guard among >= 0 - 5 && among <= 0 else Share(0)
                    Share(Rational.toInt(DOWN, amount / among))"""));
    }

    /**
     * A quotient no decimal writes is held outward at each end: a third lies between nought and
     * one, so a share of one among three is at most one and at least nought, and not more than
     * that.
     *
     * <p>The mode is not read, so the two ends are the same for every mode. Each is left owed under
     * the mode that lands on the other: a third rounded down is nought, and rounded up it is one.
     */
    @Test
    void aQuotientNoDecimalWritesIsHeldOutward() {
        String oneAmongThree = """
                guard amount == 1 else Share(%2$s)
                    guard among == 3 else Share(%2$s)
                    Share(Rational.toInt(%1$s, amount / among))""";
        for (String mode : List.of("DOWN", "CEILING")) {
            assertEquals(List.of(),
                    reported("value >= 0 && value <= 1", oneAmongThree.formatted(mode, "1")), mode);
        }
        assertEquals(List.of("E2011"), reported("value >= 1", oneAmongThree.formatted("DOWN", "1")),
                "a third rounded down is nought");
        assertEquals(List.of("E2011"),
                reported("value <= 0", oneAmongThree.formatted("CEILING", "0")),
                "a third rounded up is one");
    }

    /** The construction refused where the inputs are pinned to {@code amount} and {@code among},
     * which is a share there that the invariant fails. Only for a quotient that is a whole number:
     * the mode is not read, so one that is not lands on either of two. The share the guards depart
     * with is asked first, so the refusal is the quotient's and not theirs. */
    private static void refusedAt(String bounds, int amount, String among) {
        assertEquals(List.of(), reported(bounds, "Share(1)"),
                "the share the guards depart with is one the invariant fails, and would be refused");
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileWithWarnings(model(bounds, """
                        guard amount == %d else Share(1)
                            guard among == %s else Share(1)
                            Share(Rational.toInt(DOWN, amount / among))""".formatted(amount, among))),
                "no share the invariant fails at amount " + amount + " among " + among);
        assertEquals("E2010", refused.getMessage().substring(0, 5), refused.getMessage());
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
