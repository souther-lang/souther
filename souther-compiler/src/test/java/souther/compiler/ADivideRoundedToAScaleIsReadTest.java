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
     * The scale is what the reading holds it to and not what was written at the call.
     *
     * <p>A guard settling the scale is a scale, exactly as a written number is. Asked where the
     * recipe was recorded, this could only see what folded there, so a scale the model settles was a
     * scale no reading could recover — which is the same rule turning on where a value was written
     * rather than on what it is. What is owed here is an upper end, which the sign alone does not
     * give: the reading that holds the scale to nothing gets the half that needs no grid, and that
     * half does not discharge this.
     */
    @Test
    void aScaleAGuardSettlesIsAScale() {
        String model = """
                module demo

                data Rate = Decimal
                    invariant inRange = value >= 0m && value <= 100m

                data Bad

                behavior share : (x: Decimal, y: Decimal, places: Int) -> Rate | Bad
                    constructs Rate
                let share (x, y, places) = {
                    guard x >= 0m else Bad
                    guard x <= 10m else Bad
                    guard y >= 1m else Bad
                    guard places == 2 else Bad
                    match Decimal.divide(x, y, places, HALF_UP) with
                        | Decimal as q -> Rate(q)
                        | DivisionByZero -> unreachable "y >= 1"
                }
                """;
        assertEquals(List.of(), Compiler.compileWithWarnings(model).warnings().stream()
                .map(Diagnostic::code).distinct().toList(),
                "ten at most over one at least is ten at most, and at two places it lands on that"
                        + " grid — which is the upper end, and needs the scale rather than the sign");
    }

    /**
     * A scale no {@code int} holds is no scale here, and the range is not stated.
     *
     * <p>The backend narrows the scale to a Java {@code int} before it divides (#976), so a place
     * count outside that is a division at a scale nothing proved here was about — a proof over the
     * number as written would be a proof about a different division. The same model at two places
     * discharges, which is what says this is the scale being refused and not the shape of the
     * behavior.
     */
    @Test
    void aScaleTheRunTimeCannotDivideAtIsNoScale() {
        assertEquals(List.of("E2011"), atScale("4294967298"));
        assertEquals(List.of(), atScale("2"));
    }

    /**
     * A scale wider than a reading will lay a grid out for is no scale here either.
     *
     * <p>Two questions and not one. What the run time divides at is settled by the backend; what a
     * reading can afford to lay out is the compilation's
     * ({@link souther.compiler.check.ReadingPolicy}). A million places is a number a megabyte wide
     * at every corner of one divide, and the far ends of the whole-number range are scales
     * {@code BigDecimal} refuses outright — which, asked only whether the run time takes them,
     * arrived as an exception and left the whole behavior saying nothing.
     */
    @Test
    void aScaleWiderThanAReadingLaysOutIsNoScale() {
        assertEquals(List.of("E2011"), atScale("1000000"));
        assertEquals(List.of("E2011"), atScale("0 - 1000000"));
        assertEquals(List.of("E2011"), atScale("0 - 2147483648"));
        assertEquals(List.of("E2011"), atScale("2147483647"));
    }

    /** The model of {@link #aScaleAGuardSettlesIsAScale}, with the scale written at the call. */
    private static List<String> atScale(String places) {
        return Compiler.compileWithWarnings("""
                module demo

                data Rate = Decimal
                    invariant inRange = value >= 0m && value <= 100m

                data Bad

                behavior share : (x: Decimal, y: Decimal) -> Rate | Bad
                    constructs Rate
                let share (x, y) = {
                    guard x >= 0m else Bad
                    guard x <= 10m else Bad
                    guard y >= 1m else Bad
                    match Decimal.divide(x, y, %s, HALF_UP) with
                        | Decimal as q -> Rate(q)
                        | DivisionByZero -> unreachable "y >= 1"
                }
                """.formatted(places)).warnings().stream()
                .map(Diagnostic::code).distinct().toList();
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
