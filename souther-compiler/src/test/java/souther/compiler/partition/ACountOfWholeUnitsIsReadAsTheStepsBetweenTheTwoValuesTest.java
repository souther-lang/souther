package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import souther.runtime.Temporals;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.LongPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A comparison of a count of whole units draws the line of the seconds the count comes to.
 *
 * <p>{@code DateTime.minutesBetween} drops what is left of a minute toward zero, so a second before
 * is no minute before and the count is not the difference of the two. What a comparison of it states
 * is exact all the same, and the rows built for it are held against the run time's own count.
 */
class ACountOfWholeUnitsIsReadAsTheStepsBetweenTheTwoValuesTest {

    private static final String PARAMETERS = "a: DateTime, b: DateTime";

    /** Each relation against a count above nought, in seconds from the first value to the second. */
    @Test
    void everyRelationIsTheStepsItComesTo() {
        assertEquals(List.of("b - 660"), bordersOf("DateTime.minutesBetween(a, b) > 10"));
        assertEquals(List.of("b - 600"), bordersOf("DateTime.minutesBetween(a, b) >= 10"));
        assertEquals(List.of("b - 660"), bordersOf("DateTime.minutesBetween(a, b) <= 10"));
        assertEquals(List.of("b - 600"), bordersOf("DateTime.minutesBetween(a, b) < 10"));
        assertEquals(List.of("b - 600", "b - 660"),
                bordersOf("DateTime.minutesBetween(a, b) == 10"));
        assertEquals(List.of("b - 600", "b - 660"),
                bordersOf("DateTime.minutesBetween(a, b) /= 10"));
    }

    /** Below nought, a unit's worth less one step: the count of nought runs from -59 to 59. */
    @Test
    void belowNoughtTheCountTruncatesTowardNought() {
        assertEquals(List.of("b + 59"), bordersOf("DateTime.minutesBetween(a, b) >= 0"));
        assertEquals(List.of("b + 59"), bordersOf("DateTime.minutesBetween(a, b) > -1"));
        assertEquals(List.of("b + 59"), bordersOf("DateTime.minutesBetween(a, b) <= -1"));
        assertEquals(List.of("b + 119"), bordersOf("DateTime.minutesBetween(a, b) < -1"));
        assertEquals(List.of("b + 59", "b - 60"),
                bordersOf("DateTime.minutesBetween(a, b) == 0"));
        assertEquals(List.of("b + 119", "b + 59"),
                bordersOf("DateTime.minutesBetween(a, b) == -1"));
    }

    @Test
    void theCountWrittenOnTheRightOrBehindANameIsTheSameRule() {
        assertEquals(bordersOf("DateTime.minutesBetween(a, b) > 10"),
                bordersOf("10 < DateTime.minutesBetween(a, b)"));
        assertEquals(bordersOf("DateTime.minutesBetween(a, b) > 10"),
                bordersOfModel("""
                        module demo

                        data Ok
                        data No

                        behavior f : (a: DateTime, b: DateTime) -> Ok | No
                        let f (a, b) = {
                            let late = DateTime.minutesBetween(a, b)
                            guard late > 10 else No
                            Ok
                        }
                        """));
    }

    /** The two values in the other order are the line from the other end. */
    @Test
    void theValuesTheOtherWayRoundDrawTheLineTheOtherWayRound() {
        assertEquals(List.of("a - 660"), bordersOf("DateTime.minutesBetween(b, a) > 10"));
    }

    /**
     * The rows built at a count's line stand on both sides of it, as the run time counts them.
     *
     * <p>A threshold worked out as a floor is the right one for every row where the second value is
     * later and the wrong one for the rest, so what is held here is the count the run time answers
     * for the rows that were built, and not the line they were built for.
     */
    @Test
    void theRowsBuiltStandOnBothSidesOfTheCountAsTheRunTimeCountsIt() {
        for (String relation : List.of("> 10", ">= 0", "== 0", "== -1", "< -1")) {
            LongPredicate holds = switch (relation) {
                case "> 10" -> count -> count > 10;
                case ">= 0" -> count -> count >= 0;
                case "== 0" -> count -> count == 0;
                case "== -1" -> count -> count == -1;
                default -> count -> count < -1;
            };
            Set<Boolean> sides = new TreeSet<>();
            for (LocalDateTime[] pair : rowsOf("DateTime.minutesBetween(a, b) " + relation)) {
                sides.add(holds.test(Temporals.minutesBetween(pair[0], pair[1])));
            }
            assertEquals(Set.of(false, true), sides,
                    () -> "rows on both sides of: minutesBetween(a, b) " + relation);
        }
    }

    /** Every certified row's pair of date-times, in the order the parameters are written. */
    private static List<LocalDateTime[]> rowsOf(String condition) {
        List<LocalDateTime[]> pairs = new ArrayList<>();
        for (BorderAssessment border : linesOf(condition)) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        var inputs = certified.row().inputs();
                        pairs.add(new LocalDateTime[] {dateTimeIn(inputs.get(0).text()),
                                dateTimeIn(inputs.get(1).text())});
                    }
                }
            }
        }
        return pairs;
    }

    /** The date-time a fixture is written as: {@code DateTime("2026-01-01T00:00:00")}. */
    private static LocalDateTime dateTimeIn(String text) {
        int open = text.indexOf('"');
        return LocalDateTime.parse(text.substring(open + 1, text.indexOf('"', open + 1)));
    }

    private static List<String> bordersOf(String condition) {
        return linesOf(condition).stream().map(BorderAssessment::value).toList();
    }

    private static List<String> bordersOfModel(String model) {
        return linesOfModel(model).stream().map(BorderAssessment::value).toList();
    }

    private static List<BorderAssessment> linesOf(String condition) {
        return linesOfModel("""
                module demo

                data Ok
                data No

                behavior f : (%s) -> Ok | No
                let f (a, b) = {
                    guard %s else No
                    Ok
                }
                """.formatted(PARAMETERS, condition));
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
