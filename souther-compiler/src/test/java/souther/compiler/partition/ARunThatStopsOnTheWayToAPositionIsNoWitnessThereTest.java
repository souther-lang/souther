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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position is read as reached at every value only over values some run gets to it at. The
 * statements on the way are kept as the form they state, and the arithmetic that wrote one can stop
 * at a partial sum that form does not show. What the operators of the run narrow is read as a
 * statement of the way that says the same is: a value the first sum stops on is a value no run
 * reaches the membership at, as a guard keeping it out would say.
 */
class ARunThatStopsOnTheWayToAPositionIsNoWitnessThereTest {

    private static final String READ = "rule_relating_two_values";

    private static final String NOT_SHOWN = "relation_not_shown_to_reach_every_value";

    private static final String PARAMETERS = "a: Int, d: Int, hs: Set<Int>";

    private static final String MEMBERSHIP = "Bool.not(Set.contains(a, hs))";

    /** The greatest {@code Int}, which {@code a + FIRST_SUM} reaches at {@code a == 10}. */
    private static final long FIRST_SUM = 9223372036854775797L;

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String THE_SUM_STOPPING =
            "a + " + FIRST_SUM + " - d >= 0 && " + MEMBERSHIP;

    private static final String THE_REMAINDER_OF_A_SUM_STOPPING =
            "Int.floorMod(" + FIRST_SUM + " + a - d, 7) >= 1 && " + MEMBERSHIP;

    private static final String THE_SUM_CANCELLING_TO_THE_FORM =
            "Int.floorMod(a + 9223372036854775807 - 9223372036854775807 - d, 7) >= 1 && "
                    + MEMBERSHIP;

    /** Every one of the three stops the first addition at {@code a} from 11 up. */
    @Test
    void theElementsOfAMembershipBesideASumThatStopsAreNotShownReached() {
        for (String condition : List.of(THE_SUM_STOPPING, THE_REMAINDER_OF_A_SUM_STOPPING)) {
            assertEquals(List.of(NOT_SHOWN), reasonsAt(PARAMETERS, condition, "hs[*]"), condition);
            assertFalse(reasonsAt(PARAMETERS, condition, "a").isEmpty(), condition);
        }
        assertEquals(List.of(NOT_SHOWN), reasonsAt(PARAMETERS, THE_SUM_CANCELLING_TO_THE_FORM,
                "hs[*]"));
    }

    /**
     * The values the sum stops on: {@code a} at 11 is past the greatest {@code Int} and at 10 is
     * the greatest, so a row the compiler offers for the rule is one the program gets past, and
     * the rows beside the stop hold the element on each side of it.
     */
    @Test
    void theRowsOfferedAreRunsThatGetPastTheSumAndAreDrawnAtItsEdge() {
        assertThrows(ArithmeticException.class, () -> Math.addExact(11L, FIRST_SUM));
        assertEquals(Long.MAX_VALUE, Math.addExact(10L, FIRST_SUM));
        for (String condition : List.of(THE_SUM_STOPPING, THE_REMAINDER_OF_A_SUM_STOPPING)) {
            List<List<String>> rows = certifiedRowsOf(condition);
            assertFalse(rows.isEmpty(), condition);
            TreeSet<Long> elements = new TreeSet<>();
            for (List<String> row : rows) {
                long a = Long.parseLong(row.get(0));
                Math.addExact(a, FIRST_SUM);
                for (String element : row.get(2).replaceAll("[\\[\\]\\s]", "").split(",")) {
                    if (!element.isEmpty()) {
                        elements.add(Long.parseLong(element));
                    }
                }
            }
            assertTrue(elements.contains(10L) && elements.contains(11L),
                    condition + " " + elements);
        }
    }

    /**
     * The sum is worked out only on the runs where {@code d} is above nought, and the membership is
     * reached on the others without it, so no sum stops a run there.
     */
    @Test
    void aSumWorkedOutInAnArmTheMembershipIsReachedWithoutIsNoStop() {
        String condition = "(d > 0 && a + " + FIRST_SUM + " - d >= 0) || " + MEMBERSHIP;
        assertEquals(List.of(READ), reasonsAt(PARAMETERS, condition, "hs[*]"));
    }

    /** The same sum as the left arm of a choice, worked out on every run before the membership. */
    @Test
    void aSumTheLeftArmOfAChoiceWorksOutOnEveryRunIsAStopThere() {
        String condition = "(a + " + FIRST_SUM + " - d >= 0 || d > 0) && " + MEMBERSHIP;
        assertEquals(List.of(NOT_SHOWN), reasonsAt(PARAMETERS, condition, "hs[*]"));
    }

    /**
     * A choice whose left arm is a sum tying two numbers narrows both on the way it is not taken,
     * and a run read off that region can reach past the ends of the type. A relation after it is
     * read all the same, whether a comparison or a membership.
     */
    @Test
    void aRelationAfterASumThatTiesTwoNumbersIsReadWhereTheTypeEnds() {
        String choice = "(a + " + FIRST_SUM + " - d >= 0 || d > 0) && ";
        assertEquals(Map.of("a", List.of(READ), "d", List.of(READ)),
                readingsOf(NUMBERS, choice + "a - b > 0"));
        assertEquals(Map.of("a", List.of(READ), "d", List.of(READ), "b", List.of(NOT_SHOWN)),
                readingsOf(NUMBERS, choice + "a == b"));
        assertEquals(Map.of("a", List.of(NOT_SHOWN, READ), "d", List.of(READ)),
                readingsOf(NUMBERS, choice + "a * b >= 0"));
        assertEquals(Map.of("a", List.of(READ), "d", List.of(READ), "hs[*]", List.of(NOT_SHOWN)),
                readingsOf(NUMBERS, choice + MEMBERSHIP));
        assertEquals(Map.of("a", List.of(NOT_SHOWN, READ), "d", List.of(READ)),
                readingsOf(NUMBERS, choice + "Int.floorMod(a, b) == 0"));
    }

    /**
     * Worked out as the program does, {@code a + K - K} stops at {@code a} from 11 up; as a form it
     * is {@code a}. The membership of the one is not the membership of the other, and reads as the
     * guard keeping {@code a} to 10 or less does: what the argument works out is the relation's
     * own, and the region it narrows is what the reader of the relation is handed.
     */
    @Test
    void aSumAnArgumentStopsAtIsNotTheArgumentItIsAsAForm() {
        String written = "Bool.not(Set.contains(a + " + FIRST_SUM + " - " + FIRST_SUM + ", hs))";
        assertEquals(List.of(READ), reasonsAt(PARAMETERS, MEMBERSHIP, "hs[*]"));
        assertEquals(Map.of("a", List.of(NOT_SHOWN), "hs[*]", List.of(NOT_SHOWN)),
                readingsOf(PARAMETERS, written));
        assertEquals(readingsOf(PARAMETERS, "a <= 10 && " + written),
                readingsOf(PARAMETERS, written));
        String withTheDifference = "Bool.not(Set.contains(a + " + FIRST_SUM + " - " + FIRST_SUM
                + " - d, hs))";
        assertEquals(readingsOf(PARAMETERS, "a <= 10 && Bool.not(Set.contains(a - d, hs))"),
                readingsOf(PARAMETERS, withTheDifference));
    }

    /**
     * A comparison works out a sum, and where the sum is more than the form the comparison is
     * about, it stops a run at an {@code a} the form has a row at: {@code a + K - K == b} is
     * {@code a == b} to the form, and no run with {@code a} past 10 gets past the first sum. That
     * is a line the model draws and is read as the guard that says the same is. A sum that is the
     * form itself stops where the form's own addends pass the type, which is the representation
     * running out for any {@code K}, and is read as {@code a + 1 == b} is.
     */
    @Test
    void aSumBeyondTheFormAComparisonIsAboutStopsARunAtALineOfTheModel() {
        String k = Long.toString(Long.MAX_VALUE - 10);
        for (String beyond : List.of("a + K - K == b", "a + K - 100 == b", "a + K == b + 1")) {
            String written = beyond.replace("K", k);
            assertEquals(readingsOf(NUMBERS, "a <= 10 && " + written),
                    readingsOf(NUMBERS, written), beyond);
            assertEquals(List.of(NOT_SHOWN), reasonsAt(NUMBERS, written, "b"), beyond);
        }
        for (String theForm : List.of("a + K == b", "a + K - b > 0", "a + 1 == b",
                "a < b + 1")) {
            assertEquals(Map.of("a", List.of(READ), "b", List.of(READ)),
                    readingsOf(NUMBERS, theForm.replace("K", k)), theForm);
        }
    }

    /** A form worked out wherever the rest stand keeps being read. */
    @Test
    void aFormThatIsWorkedOutEverywhereIsStillRead() {
        assertEquals(List.of(READ), reasonsAt(PARAMETERS,
                "Int.floorMod(a - d, 7) >= 1 && Bool.not(Set.contains(d, hs))", "hs[*]"));
    }

    /**
     * A relation that works out something itself does not lose what the run before it narrows.
     * {@code a + FIRST_SUM} stops at 11, and {@code a - b > 0} is a relation with an operation of
     * its own: {@code b} is divided there as it is by a guard keeping {@code a} to 10 or less.
     */
    @Test
    void whatTheRunNarrowsIsHeldBesideARelationThatWorksOutSomethingItself() {
        String stop = "a + " + FIRST_SUM + " - a >= 0 && ";
        for (String target : List.of("a - b > 0", "a + b - 100 >= 0", "a - b + 1 > 0")) {
            Map<String, List<String>> held = readingsOf(NUMBERS, stop + target);
            assertEquals(readingsOf(NUMBERS, "a <= 10 && " + target), held, target);
            assertFalse(held.getOrDefault("b", List.of()).contains(READ), target + " " + held);
        }
    }

    /**
     * A stop is read as the guard that says the same. The forms are those where the two are
     * read alike; a form where the guard is the more cautious is not among them, since the guard
     * makes every number it names no free number and the stop leaves one that takes two values.
     */
    @Test
    void aStopOfTheRunIsReadAsAGuardThatStatesTheSame() {
        for (String target : List.of(
                "a - b > 0", "a + b - 100 >= 0", "a + b + c >= 0", "a - b - c > 0", "a == b",
                "a + 1 == b", "a * b >= 0", "a * a >= 0", "a * 3 - b >= 0",
                "Int.floorMod(a - b, 7) >= 1", "Int.floorMod(a - b, 7) == 3",
                "Int.floorMod(a, 7) == 3", "Int.floorMod(b, 7) == 3", "Int.floorMod(a, b) == 0",
                "Int.floorMod(b, a) == 0", "Bool.not(Set.contains(a, hs))",
                "Bool.not(Set.contains(b, hs))", "Bool.not(Set.contains(a + b, hs))",
                "Set.size(hs) == a", "Set.size(hs) == b", "List.any(x -> x == a, xs)",
                "List.any(x -> x == b, xs)", "a - b > 0 || c > 0", "c > 0 && a - b > 0",
                "a == b && b == c", "a + b - 100 >= 0 && Bool.not(Set.contains(b, hs))")) {
            assertAsAGuardReads(10, target);
        }
        for (String target : List.of(
                "Int.floorMod(a - b, 7) >= 1 && Bool.not(Set.contains(a, hs))",
                "Int.floorMod(a + b + c, 7) >= 1 && Bool.not(Set.contains(c, hs))",
                "Int.floorMod(a + b, 7) >= 1 && Bool.not(Set.contains(b, hs))",
                "Int.floorMod(b - a, 7) >= 1 && Bool.not(Set.contains(b, hs))")) {
            assertAsAGuardReads(3, target);
        }
    }

    private static final String NUMBERS =
            "a: Int, b: Int, c: Int, d: Int, hs: Set<Int>, xs: List<Int>";

    private static void assertAsAGuardReads(int limit, String target) {
        String stop = "a + " + (Long.MAX_VALUE - limit) + " - a >= 0 && " + target;
        String guard = "a <= " + limit + " && " + target;
        assertEquals(readingsOf(NUMBERS, guard), readingsOf(NUMBERS, stop),
                () -> "at " + limit + ": " + target);
    }

    /** What each position of {@code f} is said, a reason once, by position. */
    private static Map<String, List<String>> readingsOf(String parameters, String condition) {
        JsonNode report = reportOf(compiled(parameters, condition));
        Map<String, Set<String>> found = new LinkedHashMap<>();
        collect(report, found);
        Map<String, List<String>> out = new LinkedHashMap<>();
        found.forEach((position, reasons) -> {
            reasons.remove("rule_cuts_nothing");
            if (!reasons.isEmpty()) {
                out.put(position, List.copyOf(reasons));
            }
        });
        return out;
    }

    private static void collect(JsonNode node, Map<String, Set<String>> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason") && node.has("position")) {
            out.computeIfAbsent(node.path("position").asString(), _ -> new TreeSet<>())
                    .add(node.path("reason").asString());
        }
        node.forEach(child -> collect(child, out));
    }

    private static List<String> reasonsAt(String parameters, String condition, String position) {
        return readingsOf(parameters, condition).getOrDefault(position, List.of());
    }

    /** The inputs of every row the compiler certifies for {@code f}, as the text of each. */
    private static List<List<String>> certifiedRowsOf(String condition) {
        Compilation compilation = compiled(PARAMETERS, condition);
        List<List<String>> out = new ArrayList<>();
        for (BorderAssessment border : Adequacy.readingsOf(compilation.db(), "demo").get("f")) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        out.add(certified.row().inputs().stream().map(each -> each.text())
                                .toList());
                    }
                }
            }
        }
        return out;
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
