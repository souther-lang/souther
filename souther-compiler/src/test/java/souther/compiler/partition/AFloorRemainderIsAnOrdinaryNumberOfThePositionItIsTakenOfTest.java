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
