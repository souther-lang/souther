package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;
import souther.runtime.CEILING;
import souther.runtime.DOWN;
import souther.runtime.DecimalMath;
import souther.runtime.FLOOR;
import souther.runtime.HALF_DOWN;
import souther.runtime.HALF_EVEN;
import souther.runtime.HALF_UP;
import souther.runtime.Rational;
import souther.runtime.RationalMath;
import souther.runtime.RoundingMode;
import souther.runtime.UP;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.LongPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of a number rounded to a whole one draws the line of the number before it was
 * rounded.
 *
 * <p>{@code Rational.toInt} and {@code Decimal.toInt} answer a step of what they round, so the
 * rounded number is no form of it. What a comparison of it states is exact all the same, and the
 * rows built for it are held against the run time's own rounding.
 */
class AComparisonOfARoundedNumberIsReadAsALineOnWhatWasRoundedTest {

    @Test
    void theRoundedComparisonIsTheComparisonOfTheNumberAtTheLineItsWayOfRoundingPuts() {
        assertEquals(bordersOf("x / 2 >= 100"), bordersOf("Rational.toInt(DOWN, x / 2) >= 100"));
        assertEquals(bordersOf("x / 2 >= 100"), bordersOf("Rational.toInt(FLOOR, x / 2) >= 100"));
        assertEquals(bordersOf("x / 2 > 99"), bordersOf("Rational.toInt(CEILING, x / 2) >= 100"));
        assertEquals(bordersOf("x / 2 > 99"), bordersOf("Rational.toInt(UP, x / 2) >= 100"));
        assertEquals(bordersOf("x >= 199"), bordersOf("Rational.toInt(HALF_UP, x / 2) >= 100"));
        assertEquals(bordersOf("x > 199"), bordersOf("Rational.toInt(HALF_DOWN, x / 2) >= 100"));
        assertEquals(bordersOf("x >= 199"), bordersOf("Rational.toInt(HALF_EVEN, x / 2) >= 100"));
        assertEquals(bordersOf("x > 201"), bordersOf("Rational.toInt(HALF_EVEN, x / 2) >= 101"));
    }

    /** Toward nought and away from it part at the sign of the threshold. */
    @Test
    void atOrBelowNoughtTowardNoughtAndAwayFromItTradePlaces() {
        assertEquals(bordersOf("x / 2 > -1"), bordersOf("Rational.toInt(DOWN, x / 2) >= 0"));
        assertEquals(bordersOf("x / 2 >= 0"), bordersOf("Rational.toInt(UP, x / 2) >= 0"));
        assertEquals(bordersOf("x > -1"), bordersOf("Rational.toInt(HALF_UP, x / 2) >= 0"));
        assertEquals(bordersOf("x >= -1"), bordersOf("Rational.toInt(HALF_DOWN, x / 2) >= 0"));
    }

    @Test
    void everyRelationIsAtLeastOneThresholdOrTheNext() {
        String rounded = "Rational.toInt(HALF_EVEN, x / 2)";
        assertEquals(List.of("201"), bordersOf(rounded + " > 100"));
        assertEquals(List.of("199"), bordersOf(rounded + " < 100"));
        assertEquals(List.of("201"), bordersOf(rounded + " <= 100"));
        // Two lines a rule draws stand where its comparison does, so they are listed by what they
        // are at rather than in the order a source would have written them.
        assertEquals(Set.copyOf(bordersOf("x / 2 >= 99.5m && x / 2 <= 100.5m")),
                Set.copyOf(bordersOf(rounded + " == 100")));
        assertEquals(Set.copyOf(bordersOf("x / 2 < 99.5m || x / 2 > 100.5m")),
                Set.copyOf(bordersOf(rounded + " /= 100")));
    }

    @Test
    void theRoundingWrittenOnTheRightOrBehindANameIsTheSameRule() {
        assertEquals(bordersOf("Rational.toInt(HALF_UP, x / 2) > 100"),
                bordersOf("100 < Rational.toInt(HALF_UP, x / 2)"));
        assertEquals(bordersOf("Rational.toInt(HALF_DOWN, x / 2) >= 100"), bordersOfBody("""
                    let mode = HALF_DOWN
                    let avg = Rational.toInt(mode, x / 2)
                    guard avg >= 100 else No
                    Ok
                """));
    }

    @Test
    void aDecimalIsRoundedTheSameWay() {
        assertEquals(List.of("2.5"), linesOfModel("""
                module demo

                data Ok
                data No

                behavior f : (d: Decimal) -> Ok | No
                let f (d) = {
                    guard Decimal.toInt(HALF_UP, d) >= 3 else No
                    Ok
                }
                """).stream().map(BorderAssessment::value).toList());
    }

    /**
     * A line at a half below a threshold past what a signed 64-bit number says is the decimal it is,
     * and not a comparison left unread for want of a number to write it with.
     */
    @Test
    void aLineAtAHalfPastALongIsTheDecimalItIs() {
        assertEquals(List.of("5999999999999999999.5"), linesOfModel("""
                module demo

                data Ok
                data No

                behavior f : (d: Decimal) -> Ok | No
                let f (d) = {
                    guard Decimal.toInt(HALF_UP, d) >= 6000000000000000000 else No
                    Ok
                }
                """).stream().map(BorderAssessment::value).toList());
    }

    /**
     * A rounding built as a newtype and held against a value of it is the rounding held against the
     * number, as the arithmetic reads a newtype: an average of pay rounded down to whole yen.
     */
    @Test
    void aRoundingUnderANewtypeIsTheSameRule() {
        assertEquals(bordersOf("x / 3 >= 100"), bordersOfModel("""
                module demo

                data Yen = Int
                data Ok
                data No

                behavior f : (x: Int) -> Ok | No
                let f (x) = {
                    let average = Yen(Rational.toInt(DOWN, x / 3))
                    guard average >= Yen(100) else No
                    Ok
                }
                """));
    }

    /** The comparison the issue was about is read, and the measurement of it is complete. */
    @Test
    void theRoundedAverageIsReadAndItsMeasurementIsComplete() {
        String report = human("""
                module demo

                data Low

                behavior decide : (x: Int) -> Int | Low

                let decide (x) = {
                    let avg = Rational.toInt(DOWN, x / 2)
                    guard avg >= 100 else Low
                    avg
                }
                """);
        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("not read"), report);
    }

    /**
     * A rounding held above a whole number is the number before rounding at or above the next one:
     * {@code Rational.toInt(DOWN, x / 2) > 100} is {@code x / 2 >= 101}, whose value holds where the
     * value the source wrote does not. The line drawn is the rule's, and every point of it is one a
     * row is asked for, on whichever side the source wrote the rounding.
     */
    @Test
    void aLineWhoseValueHoldsWhereTheWrittenOnesDoesNotIsMeasuredInFull() {
        for (String condition : List.of("Rational.toInt(DOWN, x / 2) > 100",
                "100 < Rational.toInt(DOWN, x / 2)", "Rational.toInt(DOWN, x / 2) <= 100",
                "Rational.toInt(CEILING, x / 2) >= 100")) {
            String report = human("""
                    module demo

                    data Low

                    behavior decide : (x: Int) -> Int | Low

                    let decide (x) = {
                        guard %s else Low
                        x
                    }
                    """.formatted(condition));
            assertTrue(report.contains("measurement: complete"), condition + "\n" + report);
            assertFalse(report.contains("nothing could show"), condition + "\n" + report);
        }
    }

    /** A way of rounding the run chooses is read on each way the run can take to it. */
    @Test
    void aWayOfRoundingTheRunChoosesIsReadOnEachPathToIt() {
        assertEquals(List.of("200", "198"), bordersOfModel("""
                module demo

                data Ok
                data No

                behavior f : (x: Int, b: Bool) -> Ok | No
                let f (x, b) = {
                    let mode = if b then DOWN else UP
                    guard Rational.toInt(mode, x / 2) >= 100 else No
                    Ok
                }
                """));
    }

    /** What was rounded is read as any number is: a product of two inputs is no line. */
    @Test
    void aRoundingOfWhatNoFormSaysDrawsNoLine() {
        assertEquals(List.of(), bordersOf("Rational.toInt(DOWN, x * x / 2) >= 100"));
    }

    /**
     * The rows built at a rounded number's line stand on both sides of it, as the run time rounds
     * them.
     *
     * <p>An exact half is where the ways that round to the nearer number part, so a line a half off
     * or on the wrong side of its half is the right one for every row but the half, and what is held
     * here is the rounding the run time answers for the rows that were built.
     */
    @Test
    void theRowsBuiltStandOnBothSidesOfTheRoundingAsTheRunTimeRoundsIt() {
        for (RoundingMode mode : List.of(HALF_UP.INSTANCE, HALF_EVEN.INSTANCE, HALF_DOWN.INSTANCE,
                UP.INSTANCE, DOWN.INSTANCE, CEILING.INSTANCE, FLOOR.INSTANCE)) {
            String way = RoundingMode.__tag(mode);
            for (String relation : List.of(">= 100", ">= 101", ">= 0", "== -1", "< -3")) {
                LongPredicate holds = switch (relation) {
                    case ">= 100" -> rounded -> rounded >= 100;
                    case ">= 101" -> rounded -> rounded >= 101;
                    case ">= 0" -> rounded -> rounded >= 0;
                    case "== -1" -> rounded -> rounded == -1;
                    default -> rounded -> rounded < -3;
                };
                String condition = "Rational.toInt(" + way + ", x / 2) " + relation;
                Set<Boolean> sides = new TreeSet<>();
                for (long x : rowsOf(condition)) {
                    sides.add(holds.test(RationalMath.toInt(mode,
                            Rational.of(BigInteger.valueOf(x), BigInteger.TWO))));
                }
                assertEquals(Set.of(false, true), sides, () -> "rows on both sides of: " + condition);
            }
        }
    }

    /**
     * The same of a decimal, whose line at a half is the decimal taken twice against a whole number
     * and whose rows are decimals.
     */
    @Test
    void theRowsBuiltForADecimalStandOnBothSidesOfItsRounding() {
        for (RoundingMode mode : List.of(HALF_UP.INSTANCE, HALF_EVEN.INSTANCE, DOWN.INSTANCE)) {
            String condition = "Decimal.toInt(" + RoundingMode.__tag(mode) + ", d) >= 3";
            Set<Boolean> sides = new TreeSet<>();
            for (String d : rowTextsOf(linesOfModel("""
                    module demo

                    data Ok
                    data No

                    behavior f : (d: Decimal) -> Ok | No
                    let f (d) = {
                        guard %s else No
                        Ok
                    }
                    """.formatted(condition)))) {
                sides.add(DecimalMath.toInt(mode,
                        new BigDecimal(d.substring(0, d.length() - 1))) >= 3);
            }
            assertEquals(Set.of(false, true), sides, () -> "rows on both sides of: " + condition);
        }
    }

    /** Every certified row's {@code x}. */
    private static List<Long> rowsOf(String condition) {
        return rowTextsOf(linesOf(condition)).stream().map(Long::parseLong).toList();
    }

    /** How every certified row writes its first input. */
    private static List<String> rowTextsOf(List<BorderAssessment> lines) {
        List<String> xs = new ArrayList<>();
        for (BorderAssessment border : lines) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        xs.add(certified.row().inputs().getFirst().text());
                    }
                }
            }
        }
        return xs;
    }

    private static List<String> bordersOf(String condition) {
        return linesOf(condition).stream().map(BorderAssessment::value).toList();
    }

    private static List<String> bordersOfBody(String body) {
        return bordersOfModel("""
                module demo

                data Ok
                data No

                behavior f : (x: Int) -> Ok | No
                let f (x) = {
                %s
                }
                """.formatted(body));
    }

    private static List<String> bordersOfModel(String model) {
        return linesOfModel(model).stream().map(BorderAssessment::value).toList();
    }

    private static List<BorderAssessment> linesOf(String condition) {
        return linesOfModel("""
                module demo

                data Ok
                data No

                behavior f : (x: Int) -> Ok | No
                let f (x) = {
                    guard %s else No
                    Ok
                }
                """.formatted(condition));
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<BorderAssessment> linesOfModel(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }
}
