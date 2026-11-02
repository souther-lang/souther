package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A remainder of a form of several numbers states nothing of one of them while another is free to
 * be chosen, so a membership test on one of them, read beside it, is read at every value of the
 * elements.
 *
 * <p>Free is a claim about every value of the rest: for each, some value of the free number brings
 * the form to a remainder every remainder statement of the way allows together, and the form is
 * worked out there. A remainder of one number alone, {@code Int.floorMod(d, 7) >= 1}, leaves
 * {@code d} off every seventh value, so an element at one of those never equals it.
 */
class AMembershipBesideARemainderOfTwoDatesIsReadTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** What the position is said when its elements are read: the relation leaves them undivided. */
    private static final String READ = "rule_relating_two_values";

    private static final String NOT_SHOWN = "relation_not_shown_to_reach_every_value";

    /** The number the remainder is of beside {@code d} is free, so {@code d} runs over every value. */
    @Test
    void aNumberFreeBesideTheRemainderLeavesTheElementsReached() {
        assertEquals(List.of(READ), reasonsAt("a: Int, d: Int, hs: Set<Int>",
                "Int.floorMod(a - d, 7) >= 1 && Bool.not(Set.contains(d, hs))", "hs[*]"));
        assertEquals(List.of(READ), reasonsAt("a: Int, d: Int, hs: Set<Int>",
                "Int.floorMod(a - d, 7) >= 1 && Set.contains(d, hs)", "hs[*]"));
    }

    @Test
    void theDaysBetweenTwoDatesLeaveTheElementsReached() {
        assertEquals(List.of(READ), reasonsAt("sun: Date, d: Date, hs: Set<Date>",
                "Int.floorMod(Date.daysBetween(sun, d), 7) >= 1 && Bool.not(Set.contains(d, hs))",
                "hs[*]"));
    }

    /** The two ends of a weekday are two statements of one form, and say nothing of either date. */
    @Test
    void bothEndsOfARemainderAreOneStatement() {
        assertEquals(List.of(READ), reasonsAt("sun: Date, d: Date, hs: Set<Date>",
                "Int.floorMod(Date.daysBetween(sun, d), 7) >= 1"
                        + " && Int.floorMod(Date.daysBetween(sun, d), 7) <= 5"
                        + " && Bool.not(Set.contains(d, hs))", "hs[*]"));
    }

    @Test
    void theOrderTheConjunctsAreWrittenInChangesNothing() {
        assertEquals(List.of(READ), reasonsAt("a: Int, d: Int, hs: Set<Int>",
                "Bool.not(Set.contains(d, hs)) && Int.floorMod(a - d, 7) >= 1", "hs[*]"));
    }

    /** Only {@code d} itself: an element a seventh value apart never equals it. */
    @Test
    void aRemainderOfTheDateAloneLeavesTheElementsUnshown() {
        assertEquals(List.of(NOT_SHOWN), reasonsAt("d: Int, hs: Set<Int>",
                "Int.floorMod(d, 7) >= 1 && Bool.not(Set.contains(d, hs))", "hs[*]"));
    }

    /** A number that is chosen for no one is held at a value by another statement of the way. */
    @Test
    void aNumberHeldAtOneValueIsNoNumberToChoose() {
        assertEquals(List.of(NOT_SHOWN), reasonsAt("a: Int, d: Int, hs: Set<Int>",
                "a == 0 && Int.floorMod(a - d, 7) >= 1 && Bool.not(Set.contains(d, hs))",
                "hs[*]"));
    }

    /**
     * A number that moves the remainder only to some of the remainders chooses none of the others:
     * {@code 2 * a} is even, so with {@code d} even the remainder by four is never one, and the
     * elements at an even value never equal a {@code d} that is odd.
     */
    @Test
    void aNumberThatMovesTheRemainderOnlyToSomeOfThemIsNoNumberToChoose() {
        assertEquals(List.of(NOT_SHOWN), reasonsAt("a: Int, d: Int, hs: Set<Int>",
                "Int.floorMod(2 * a - d, 4) == 1 && Bool.not(Set.contains(d, hs))", "hs[*]"));
    }

    /** The form is added up as the program adds it, which can stop a run where a number is large. */
    @Test
    void aFormTheProgramMayNotAddUpIsNotTakenAwayFromTheRun() {
        assertEquals(List.of(NOT_SHOWN), reasonsAt("a: Int, b: Int, d: Int, hs: Set<Int>",
                "Int.floorMod(a + b - d, 7) >= 1 && Bool.not(Set.contains(d, hs))", "hs[*]"));
    }

    /** Nor is a remainder taken away from a run that works the same numbers out otherwise. */
    @Test
    void aProductOfTheSameNumbersTheRunWorksOutKeepsTheirTie() {
        assertEquals(List.of(NOT_SHOWN), reasonsAt("a: Int, d: Int, hs: Set<Int>",
                "Int.floorMod(a - d, 7) >= 1 && a * d == 0 && Bool.not(Set.contains(d, hs))",
                "hs[*]"));
    }

    /** Two remainders no one number brings about together are not taken away together. */
    @Test
    void remaindersNoOneNumberBringsAboutTogetherAreNotTakenAwayTogether() {
        assertFalse(reasonsAt("a: Int, d: Int, hs: Set<Int>",
                "Int.floorMod(a - d, 7) == 1 && Int.floorMod(a - d, 7) == 2"
                        + " && Bool.not(Set.contains(d, hs))", "hs[*]").contains(READ));
    }

    /**
     * The same form moved by another number is another remainder, and the two are asked of the
     * number they share: choosing it for one is not choosing it for the other.
     */
    @Test
    void remaindersOfTheSameFormMovedByDifferentNumbersAreNotOne() {
        assertFalse(reasonsAt("a: Int, d: Int, hs: Set<Int>",
                "Int.floorMod(a - d, 7) == 1 && Int.floorMod(a - d + 1, 7) == 1"
                        + " && Bool.not(Set.contains(d, hs))", "hs[*]").contains(READ));
    }

    /**
     * The dates are fewer than the divisor has remainders, so choosing one of them cannot bring the
     * difference to each.
     */
    @Test
    void aDivisorPastTheDaysThereAreIsNotReachedByChoosingADate() {
        assertEquals(List.of(NOT_SHOWN), reasonsAt("sun: Date, d: Date, hs: Set<Date>",
                "Int.floorMod(Date.daysBetween(sun, d), 1000000000000) == 1"
                        + " && Bool.not(Set.contains(d, hs))", "hs[*]"));
    }

    /** Nor does a number held to a run another statement narrows. */
    @Test
    void aNumberAnotherStatementNarrowsIsNoNumberToChoose() {
        assertEquals(List.of(NOT_SHOWN), reasonsAt("a: Int, d: Int, hs: Set<Int>",
                "a >= 0 && a <= 3 && Int.floorMod(a - d, 7) >= 1"
                        + " && Bool.not(Set.contains(d, hs))", "hs[*]"));
    }

    /**
     * What is read at the elements is not what is owed rows: the remainder's own line still has a
     * row at it and one beside it, whose two numbers leave the remainder each says.
     */
    @Test
    void theLineOnTheRemainderIsStillOwedItsRows() {
        Compilation compilation = compiled("a: Int, d: Int, hs: Set<Int>",
                "Int.floorMod(a - d, 7) >= 1 && Bool.not(Set.contains(d, hs))");
        List<String> labels = new ArrayList<>();
        for (BorderAssessment border : Adequacy.readingsOf(compilation.db(), "demo").get("f")) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        List<String> inputs = certified.row().inputs().stream()
                                .map(each -> each.text()).toList();
                        long remainder = Math.floorMod(Math.subtractExact(
                                Long.parseLong(inputs.get(0)), Long.parseLong(inputs.get(1))), 7L);
                        certified.row().purposes().forEach(each -> each.labels().forEach(label -> {
                            if (label.startsWith("Int.floorMod(a - d, 7) = ")) {
                                assertEquals(remainder, Long.parseLong(
                                        label.substring(label.lastIndexOf(' ') + 1)), label);
                                labels.add(label);
                            }
                        }));
                    }
                }
            }
        }
        assertEquals(List.of("Int.floorMod(a - d, 7) = 0", "Int.floorMod(a - d, 7) = 1"),
                labels.stream().sorted().distinct().toList());
    }

    /** Every reason the report gives {@code position}, each once. */
    private static List<String> reasonsAt(String parameters, String condition, String position) {
        List<String> out = new ArrayList<>();
        reasons(reportOf(compiled(parameters, condition)), position, out);
        return out.stream().distinct().toList();
    }

    private static void reasons(JsonNode node, String position, List<String> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason")
                && position.equals(node.path("position").asString())) {
            out.add(node.path("reason").asString());
        }
        node.forEach(child -> reasons(child, position, out));
    }

    private static JsonNode reportOf(Compilation compilation) {
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    private static Compilation compiled(String parameters, String condition) {
        String model = """
                module demo

                behavior f : (%s) -> Bool
                let f (%s) = %s
                """.formatted(parameters, parameters.replaceAll(":\\s*[A-Za-z<>]+", ""),
                condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors());
        return compilation;
    }
}
