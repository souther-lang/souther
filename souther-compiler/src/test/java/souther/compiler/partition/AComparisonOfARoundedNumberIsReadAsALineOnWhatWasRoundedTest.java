package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.runtime.CEILING;
import souther.runtime.DOWN;
import souther.runtime.FLOOR;
import souther.runtime.HALF_DOWN;
import souther.runtime.HALF_EVEN;
import souther.runtime.HALF_UP;
import souther.runtime.Rational;
import souther.runtime.RationalMath;
import souther.runtime.RoundingMode;
import souther.runtime.UP;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.LongPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

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
        assertEquals(List.of("199", "201"), bordersOf(rounded + " == 100"));
        assertEquals(List.of("199", "201"), bordersOf(rounded + " /= 100"));
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

    /** Every certified row's {@code x}. */
    private static List<Long> rowsOf(String condition) {
        List<Long> xs = new ArrayList<>();
        for (BorderAssessment border : linesOf(condition)) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        xs.add(Long.parseLong(certified.row().inputs().getFirst().text()));
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
