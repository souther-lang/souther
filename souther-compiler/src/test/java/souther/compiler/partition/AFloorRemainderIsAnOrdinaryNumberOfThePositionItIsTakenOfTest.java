package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.LongPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule over what a division leaves is a rule over a number of the position, read and measured as
 * every other number taken of one is.
 *
 * <p>{@code Int.floorMod(x, 7) == 0} is no line on {@code x}: the values it holds of come round
 * every seventh. It is a line on the remainder, which stays between nought and the divisor, and the
 * remainder is a number of the position as the hour is a number of a time. So the border is drawn
 * on the remainder, the rows are values of the position that leave it, and what the declarations say
 * of the remainder settles which of its numbers a rule can be written at.
 */
class AFloorRemainderIsAnOrdinaryNumberOfThePositionItIsTakenOfTest {

    @Test
    void aRemainderComparedWithOneNumberDrawsTheLineAtThatNumber() {
        assertEquals(List.of("0"), bordersOf("x: Int", "Int.floorMod(x, 7) == 0"));
        assertEquals(List.of("3"), bordersOf("x: Int", "Int.floorMod(x, 7) < 3"));
        assertEquals(List.of(), reasonsOf("x: Int", "Int.floorMod(x, 7) == 0"),
                "the rule is read to the end, so nothing is left unsaid about the position");
    }

    @Test
    void aRowIsAValueThatLeavesTheRemainderTheLineIsDrawnAt() {
        assertEquals(List.of("0"), rowsAt("x: Int", "Int.floorMod(x, 7) == 0",
                "Int.floorMod(x, 7) = 0"));
        assertEquals(List.of("3"), rowsAt("x: Int", "Int.floorMod(x, 7) < 3",
                "Int.floorMod(x, 7) = 3"));
        assertEquals(List.of("2"), rowsAt("x: Int", "Int.floorMod(x, 7) < 3",
                "Int.floorMod(x, 7) = 2"));
    }

    /**
     * A remainder is never as far from nought as its divisor, so a number the divisor cannot leave
     * is one the rule cannot be written at.
     */
    @Test
    void aNumberTheDivisorCannotLeaveIsOneNoRowIsOwedAt() {
        List<BorderAssessment> lines = linesOf("x: Int", "Int.floorMod(x, 7) >= 7");
        assertEquals(List.of("7"), lines.stream().map(BorderAssessment::value).toList());
        BorderAssessment border = lines.getFirst();
        assertEquals(2, owedItems(border).size(),
                "the two points below the line are numbers the remainder reaches");
        assertEquals(2, border.items().values().stream()
                        .filter(ItemAssessment.NotOwed.class::isInstance).count(),
                "and the points on and above it are refused by the rules");
    }

    @Test
    void aNegativeDivisorLeavesTheRemainderBetweenItAndNought() {
        List<BorderAssessment> lines = linesOf("x: Int", "Int.floorMod(x, -3) == -2");
        assertEquals(List.of("-2"), lines.stream().map(BorderAssessment::value).toList());
        assertEquals(List.of("-2"), rowsAt("x: Int", "Int.floorMod(x, -3) == -2",
                "Int.floorMod(x, -3) = -2"));
        // Below the divisor is a number the remainder never is.
        assertTrue(lines.getFirst().items().values().stream()
                .anyMatch(ItemAssessment.NotOwed.class::isInstance));
    }

    @Test
    void aRemainderByOneIsNoughtAndNothingElseIsOwed() {
        List<BorderAssessment> lines = linesOf("x: Int", "Int.floorMod(x, 1) == 0");
        assertEquals(1, owedItems(lines.getFirst()).size());
    }

    /**
     * A divisor no constant gives is no period, and a divisor of nought is a call that aborts: both
     * are rules this reading does not take, and it says so rather than reading a period into them.
     */
    @Test
    void aDivisorThatIsNoConstantIsARuleAboutAValueMadeOfThePosition() {
        assertEquals(List.of(), bordersOf("x: Int, y: Int", "Int.floorMod(x, y) == 0"));
        assertEquals(List.of(), bordersOf("x: Int", "Int.floorMod(x, 0) == 0"));
        assertFalse(reasonsOf("x: Int, y: Int", "Int.floorMod(x, y) == 0").isEmpty());
        assertFalse(reasonsOf("x: Int", "Int.floorMod(x, 0) == 0").isEmpty());
    }

    /**
     * Beside a run of the position, the row is a member of the class that stands inside the run.
     *
     * <p>The values of the position are chosen after the numbers of the rule are, so a run that
     * begins where the class does not would be offered its first value and refused for the remainder
     * fixed beside it.
     */
    @Test
    void aRunOfThePositionHasItsRowAtAMemberOfTheClassInsideIt() {
        assertEquals(List.of("14"), rowsAt("x: Int, y: Int",
                "x >= 10 && x <= 20 && Int.floorMod(x, 7) == 0", "Int.floorMod(x, 7) = 0"));
        assertEquals(List.of("11"), rowsAt("x: Int, y: Int",
                "x >= 10 && x <= 20 && Int.floorMod(x, 7) == 4", "Int.floorMod(x, 7) = 4"));
        assertEquals(List.of("-14"), rowsAt("x: Int, y: Int",
                "x >= -20 && x <= -10 && Int.floorMod(x, 7) == 0", "Int.floorMod(x, 7) = 0"));
        assertEquals(List.of("17"), rowsAt("x: Int, y: Int",
                "x > 10 && Int.floorMod(x, 7) == 3", "Int.floorMod(x, 7) = 3"));
    }

    /** A run holding no member of the class is a run the rules leave nothing at. */
    @Test
    void aRunHoldingNoMemberOfTheClassIsOneTheRulesLeaveNothingAt() {
        assertEquals(List.of(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE),
                unresolvedAt("x: Int, y: Int", "x >= 10 && x <= 12 && Int.floorMod(x, 7) == 0",
                        "Int.floorMod(x, 7) = 0"));
    }

    /**
     * Two remainders of one position by two divisors are two numbers of it, and the position's own
     * run is held to both.
     */
    @Test
    void remaindersByTwoDivisorsAreTwoNumbersOfOnePosition() {
        assertEquals(List.of("0", "1"), bordersOf("x: Int",
                "Int.floorMod(x, 2) == 0 && Int.floorMod(x, 3) == 1"));
        assertEquals(List.of("10"), rowsAt("x: Int, y: Int",
                "x >= 10 && Int.floorMod(x, 2) == 0 && Int.floorMod(x, 3) == 1",
                "Int.floorMod(x, 2) = 0"));
    }

    /**
     * Divisors as wide as these have a period no walk is allowed, so a row is only there where the
     * class is solved for and not stepped to.
     */
    @Test
    void remaindersByWideDivisorsAreSolvedAndNotSteppedTo() {
        assertEquals(1, rowsAt("x: Int, y: Int",
                "Int.floorMod(x, 100003) == 3 && Int.floorMod(x, 100019) == 4",
                "Int.floorMod(x, 100003) = 3").size());
        assertEquals(List.of("7"), rowsAt("x: Int, y: Int",
                "x >= 1 && Int.floorMod(x, 1000003) == 7", "Int.floorMod(x, 1000003) = 7"));
    }

    /** One number cannot leave two remainders by one divisor: the second comparison is never
     *  reached. */
    @Test
    void aRemainderCannotBeTwoNumbersAtOnce() {
        List<PartitionEvidence.NotRead> unreached = measured("x: Int",
                "Int.floorMod(x, 7) == 0 && Int.floorMod(x, 7) == 1").notRead();
        assertEquals(1, unreached.size());
        assertTrue(unreached.getFirst().toString().contains("ComparisonNothingArrivesAtItsLine"),
                unreached.toString());
    }

    /** A remainder compared through a name is the same rule. */
    @Test
    void aRemainderNamedBeforeItIsComparedIsTheSameRule() {
        String model = """
                module demo

                data Ok
                data No

                behavior f : (x: Int) -> Ok | No
                let f (x) = {
                    let rest = Int.floorMod(x, 7)
                    guard rest == 0 else No
                    Ok
                }
                """;
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read);
        assertEquals(List.of("0"), read.get("f").stream().map(BorderAssessment::value).toList());
    }

    /**
     * A place moved by a number has the remainder the place has, moved round the divisor — however
     * the moving is spelled.
     *
     * <p>{@code Int.floorMod(x + 1, 7) == 0} is a rule about {@code x} being six more than a
     * multiple of seven, and states of {@code x} what {@code Int.floorMod(x, 7) == 6} does.
     */
    @Test
    void aPlaceMovedByANumberStatesWhatItsRemainderMovedStates() {
        for (String moved : List.of("x + 1", "1 + x", "x - 6", "Int.add(x, 1)",
                "Int.subtract(x, 6)", "Int.add(x, 8)", "x + 1 + 7", "x + 3 - 2")) {
            assertEquals(List.of("6"), bordersOf("x: Int", "Int.floorMod(" + moved + ", 7) == 0"),
                    moved);
            assertEquals(List.of("6"), rowsAt("x: Int", "Int.floorMod(" + moved + ", 7) == 0",
                    "Int.floorMod(x, 7) = 6"), moved);
        }
        // Taken from a number, the remainder runs the other way.
        assertEquals(List.of("3"), bordersOf("x: Int", "Int.floorMod(3 - x, 7) == 0"));
        assertEquals(List.of("3"), rowsAt("x: Int", "Int.floorMod(3 - x, 7) == 0",
                "Int.floorMod(x, 7) = 3"));
        assertEquals(List.of(), reasonsOf("x: Int", "Int.floorMod(x + 1, 7) == 0"));
    }

    /**
     * What the rows built say of the moved value is what the run time says of it: some of them stand
     * on the side of the comparison it holds on, and some on the other.
     *
     * <p>Checked against the library's own remainder and not against the rewriting that reads it,
     * for every relation, a moving each way and a moving past the divisor — where the remainder of
     * the place and the remainder of the moved value part at a stretch of the first.
     */
    @Test
    void theRowsBuiltForAMovedValueStandOnBothSidesOfItsOwnRemainder() {
        for (String relation : List.of("== 0", "< 2", ">= 5", "/= 3", "> 0", "<= 4")) {
            for (int by : List.of(1, 3, 6, 10, -4)) {
                LongPredicate holds = switch (relation) {
                    case "== 0" -> r -> r == 0;
                    case "< 2" -> r -> r < 2;
                    case ">= 5" -> r -> r >= 5;
                    case "/= 3" -> r -> r != 3;
                    case "> 0" -> r -> r > 0;
                    default -> r -> r <= 4;
                };
                String condition = "Int.floorMod(x + " + (by < 0 ? "(0 - " + -by + ")" : by)
                        + ", 7) " + relation;
                Set<Boolean> sides = new TreeSet<>();
                for (long x : valuesOfRowsBuiltFor(condition)) {
                    sides.add(holds.test(Math.floorMod(x + by, 7L)));
                }
                assertEquals(Set.of(false, true), sides, condition);
            }
            for (int by : List.of(0, 3, 6, 9)) {
                LongPredicate holds = switch (relation) {
                    case "== 0" -> r -> r == 0;
                    case "< 2" -> r -> r < 2;
                    case ">= 5" -> r -> r >= 5;
                    case "/= 3" -> r -> r != 3;
                    case "> 0" -> r -> r > 0;
                    default -> r -> r <= 4;
                };
                String condition = "Int.floorMod(" + by + " - x, 7) " + relation;
                Set<Boolean> sides = new TreeSet<>();
                for (long x : valuesOfRowsBuiltFor(condition)) {
                    sides.add(holds.test(Math.floorMod(by - x, 7L)));
                }
                assertEquals(Set.of(false, true), sides, condition);
            }
        }
    }

    /** The place moved by a number, named before its remainder is compared, is the same rule. */
    @Test
    void aMovedPlaceNamedBeforeItsRemainderIsComparedIsTheSameRule() {
        String model = """
                module demo

                data Ok
                data No

                behavior f : (x: Int) -> Ok | No
                let f (x) = {
                    let next = x + 1
                    guard Int.floorMod(next, 7) < 2 else No
                    Ok
                }
                """;
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<String> named = Adequacy.readingsOf(compilation.db(), "demo").get("f").stream()
                .map(BorderAssessment::value).toList();
        assertEquals(bordersOf("x: Int", "Int.floorMod(x + 1, 7) < 2"), named);
        assertEquals(List.of(), compilation.db().ask(new Adequacy.Coverage("demo")).value()
                .get("f").notRead());
    }

    /** What is scaled, or made of two places, is no place moved by a number, and a divisor below
     *  nought answers the other side of nought where the moving was worked out for this one. */
    @Test
    void whatIsNotAPlaceMovedByANumberIsLeftUnread() {
        assertEquals(List.of(), bordersOf("x: Int", "Int.floorMod(x * 2, 7) == 0"));
        assertEquals(List.of(), bordersOf("x: Int, y: Int", "Int.floorMod(x + y, 7) == 0"));
        assertEquals(List.of(), bordersOf("x: Int", "Int.floorMod(x + 1, 0 - 7) == 0"));
        assertFalse(reasonsOf("x: Int", "Int.floorMod(x * 2, 7) == 0").isEmpty());
    }

    /**
     * The remainders asked for may be sets of numbers, and the one a search tries first may be a
     * number the others rule out: the others are tried, and what is found is a number of every one.
     */
    @Test
    void aChoiceOfRemainderThatDisagreesWithAnotherIsNotTheEndOfTheSearch() {
        // A remainder of nought or one by one thousand and two, and of nine hundred ninety nine
        // thousand nine hundred ninety nine by a million: the first can only be one, and the number
        // that answers both is a long way from where a step from nought would reach.
        String condition = "Int.floorMod(x, 1000002) < 2 && Int.floorMod(x, 1000000) == 999999";
        assertFalse(valuesOfRowsBuiltFor(condition).isEmpty());
        assertEquals(0, attemptsThatBuiltNothing("x: Int, y: Int", condition),
                "every point owed a row has one");
        for (long x : rowsAtAsNumbers("x: Int, y: Int", condition,
                "Int.floorMod(x, 1000000) = 999999")) {
            assertEquals(999999L, Math.floorMod(x, 1000000L));
        }
    }

    /** The divisors a signed 64-bit number can hold are all divisors, the least and the greatest
     *  among them. */
    @Test
    void theLeastAndGreatestDivisorsAreDivisors() {
        Map<String, String> remainderBy = Map.of("9223372036854775807", "7",
                "0 - 9223372036854775807 - 1", "-7");
        remainderBy.forEach((divisor, remainder) -> {
            String condition = "Int.floorMod(x, " + divisor + ") == "
                    + (remainder.startsWith("-") ? "0 - " + remainder.substring(1) : remainder);
            assertEquals(List.of(remainder), bordersOf("x: Int", condition), condition);
            assertEquals(0, attemptsThatBuiltNothing("x: Int", condition), condition);
        });
    }

    /** How many searches of the condition's points built no row. */
    private static long attemptsThatBuiltNothing(String parameters, String condition) {
        long count = 0;
        for (BorderAssessment border : linesOf(parameters, condition)) {
            for (ItemAssessment.Owed owed : owedItems(border)) {
                count += owed.searches().each().stream()
                        .filter(each -> !(each instanceof ItemAssessment.Attempt.Certified))
                        .count();
            }
        }
        return count;
    }

    private static List<Long> rowsAtAsNumbers(String parameters, String condition, String label) {
        return rowsAt(parameters, condition, label).stream().map(Long::parseLong).toList();
    }

    /**
     * Around the point the remainder comes back to nought the run is the run, and the row is a
     * number of the class that the run reaches — above nought or below it.
     */
    @Test
    void aRunAcrossWhereTheRemainderComesRoundHasItsRowAtTheTurn() {
        assertEquals(List.of("7"), rowsAt("x: Int, y: Int",
                "x >= 6 && x <= 8 && Int.floorMod(x, 7) < 1", "Int.floorMod(x, 7) = 0"));
        assertEquals(List.of("-7"), rowsAt("x: Int, y: Int",
                "x >= -8 && x <= -6 && Int.floorMod(x, 7) < 1", "Int.floorMod(x, 7) = 0"));
        assertEquals(List.of("6"), rowsAt("x: Int, y: Int",
                "x >= 5 && x <= 7 && Int.floorMod(x, 7) == 6", "Int.floorMod(x, 7) = 6"));
        assertEquals(List.of("-1"), rowsAt("x: Int, y: Int",
                "x >= -2 && x <= 0 && Int.floorMod(x, 7) == 6", "Int.floorMod(x, 7) = 6"));
    }

    /** The first input of every certified row built for the condition, as a number. */
    private static List<Long> valuesOfRowsBuiltFor(String condition) {
        List<Long> values = new ArrayList<>();
        for (BorderAssessment border : linesOf("x: Int, y: Int", condition)) {
            for (ItemAssessment.Owed owed : owedItems(border)) {
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        values.add(Long.parseLong(certified.row().inputs().getFirst().text()));
                    }
                }
            }
        }
        return values;
    }

    private static List<ItemAssessment.Owed> owedItems(BorderAssessment border) {
        List<ItemAssessment.Owed> owed = new ArrayList<>();
        border.items().values().forEach(item -> {
            if (item instanceof ItemAssessment.Owed here) {
                owed.add(here);
            }
        });
        return owed;
    }

    /** The first input of each certified row built for the point labelled {@code label}. */
    private static List<String> rowsAt(String parameters, String condition, String label) {
        List<String> inputs = new ArrayList<>();
        for (BorderAssessment border : linesOf(parameters, condition)) {
            for (ItemAssessment.Owed owed : owedItems(border)) {
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified
                            && certified.row().purposes().stream()
                                    .anyMatch(each -> each.labels().contains(label))) {
                        inputs.add(certified.row().inputs().getFirst().text());
                    }
                }
            }
        }
        return inputs;
    }

    /** Why the search for the point labelled {@code label} came to nothing. */
    private static List<Generator.UnresolvedCombination.Reason> unresolvedAt(
            String parameters, String condition, String label) {
        List<Generator.UnresolvedCombination.Reason> reasons = new ArrayList<>();
        for (BorderAssessment border : linesOf(parameters, condition)) {
            for (ItemAssessment.Owed owed : owedItems(border)) {
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Unresolved unresolved
                            && unresolved.why().classes().contains(label)) {
                        reasons.add(unresolved.why().reason());
                    }
                }
            }
        }
        return reasons;
    }

    private static List<BorderAssessment> linesOf(String parameters, String condition) {
        Compilation compilation = compiled(parameters, condition);
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }

    private static PartitionEvidence measured(String parameters, String condition) {
        Compilation compilation = compiled(parameters, condition);
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model under test compiles");
        PartitionEvidence evidence = coverage.get("f");
        assertNotNull(evidence, "f was measured");
        assertInstanceOf(PartitionEvidence.class, evidence);
        return evidence;
    }

    private static Compilation compiled(String parameters, String condition) {
        String model = """
                module demo

                data Ok
                data No

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    guard %s else No
                    Ok
                }
                """.formatted(parameters,
                parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static List<String> bordersOf(String parameters, String condition) {
        return linesOf(parameters, condition).stream().map(BorderAssessment::value).toList();
    }

    private static List<UndividedPosition.Reason> reasonsOf(String parameters, String condition) {
        return measured(parameters, condition).notRead().stream()
                .map(PartitionEvidence.NotRead::reason).toList();
    }
}
