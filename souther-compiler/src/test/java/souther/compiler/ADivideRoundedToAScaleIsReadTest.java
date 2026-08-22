package souther.compiler;

import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@code Decimal.divide(a, b, scale, mode)} answers a number this reads, at the scale the call says.
 *
 * <p>It is the form a domain has to write when the scale and the rounding mode are its own decision:
 * there is no operator for it, so an author who wants {@code HALF_UP} at scale 0 has no spelling
 * that was read. Every other part of the round trip is — {@code fromInt}, {@code toInt} and the mode
 * are all read, and what was not is the answer of a division that comes back as a union, whichever
 * numeric type it is over (#959).
 *
 * <p>What a range says of it does not read the mode. Every mode the library has lands the answer on
 * one of the two points of the scale's grid the exact quotient lies between, so the pair is what
 * holds all seven of them.
 */
class ADivideRoundedToAScaleIsReadTest {

    private static String model(String guard, String construction) {
        return """
                module demo

                data Yen = Decimal
                    invariant nonNegD = value >= 0m

                behavior half : (x: Yen, y: Yen) -> Yen
                    constructs Yen
                let half (x, y) = {
                    guard %s else x
                    %s
                }
                """.formatted(guard, construction);
    }

    private static List<String> reported(String guard, String construction) {
        return Compiler.compileWithWarnings(model(guard, construction)).warnings().stream()
                .map(Diagnostic::code)
                .distinct()
                .toList();
    }

    /** The row the report came from. */
    @Test
    void theValueCaseIsAQuotientOfWhatItWasGiven() {
        assertEquals(List.of(), reported("y.value > 0m", """
                match Decimal.divide(x.value, y.value, 0, HALF_UP) with
                        | Decimal as q -> Yen(q)
                        | DivisionByZero -> unreachable "y > 0"
                """));
    }

    /** Whichever way it is told to round there. The mode is part of which value this is and not of
     * where it lies. */
    @Test
    void everyModeReadsAlike() {
        for (String mode : List.of("HALF_UP", "HALF_EVEN", "HALF_DOWN", "UP", "DOWN", "CEILING",
                "FLOOR")) {
            assertEquals(List.of(), reported("y.value > 0m", """
                    match Decimal.divide(x.value, y.value, 2, %s) with
                            | Decimal as q -> Yen(q)
                            | DivisionByZero -> unreachable "y > 0"
                    """.formatted(mode)), mode);
        }
    }

    /**
     * The quantisation is outward at the grid and not a step either way, which is what keeps a
     * quotient at or above nought at or above nought.
     *
     * <p>Half of a non-negative amount is at or above nought however coarse the scale is, so a scale
     * that rounds to hundreds says as much about which side of nought the answer is on as one that
     * keeps two places.
     */
    @Test
    void aCoarseScaleStillKeepsItOnItsSideOfNought() {
        assertEquals(List.of(), reported("y.value > 0m", """
                match Decimal.divide(x.value, y.value, 0 - 2, FLOOR) with
                        | Decimal as q -> Yen(q)
                        | DivisionByZero -> unreachable "y > 0"
                """));
    }

    /**
     * The control. Nothing puts the divisor on a side of nought — the guard bounds {@code y} and
     * the divide is by one less — so this rule has no divisor to fire on and the construction is
     * owed its clause.
     */
    @Test
    void withTheDivisorNotHeldOffNoughtNothingFollows() {
        assertEquals(List.of("E2011"), reported("y.value > 0m", """
                match Decimal.divide(x.value, y.value - 1m, 2, HALF_UP) with
                        | Decimal as q -> Yen(q)
                        | DivisionByZero -> Yen(0m)
                """));
    }

    /** And with the dividend on the other side of nought, what it answers is refused rather than
     * discharged: a negative amount halved is negative. */
    @Test
    void aNegativeDividendIsReportedAsBefore() {
        assertEquals(List.of("E2011"), reported("y.value > 0m", """
                match Decimal.divide(0m - x.value - 1m, y.value, 2, HALF_UP) with
                        | Decimal as q -> Yen(q)
                        | DivisionByZero -> unreachable "y > 0"
                """));
    }
}
