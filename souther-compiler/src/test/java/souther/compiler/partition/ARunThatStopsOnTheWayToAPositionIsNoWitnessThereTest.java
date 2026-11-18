package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
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

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position is read as reached at every value only over values some run gets to it at. The
 * statements on the way are kept as the form they state, and the arithmetic that wrote one can stop
 * at a partial sum that form does not show. Where it stops because the number is past where its
 * representation stops, that is no line of the model, whatever the constant that puts it there: a
 * relation after it is read as it is without it, and where the stop turns on a number the relation
 * reads, the relation is said not shown reached at every value. A guard keeping the number to the
 * same values is a statement of the model, and is read as one.
 */
class ARunThatStopsOnTheWayToAPositionIsNoWitnessThereTest {

    private static final String READ = "rule_relating_two_values";

    private static final String NOT_SHOWN = "relation_not_shown_to_reach_every_value";

    private static final String NOT_SHOWN_REACHED = "relation_not_shown_reached_at_every_value";

    private static final String NOTHING_ARRIVES = "nothing_arrives_at_the_rules_line";

    private static final String PARAMETERS = "a: Int, d: Int, hs: Set<Int>";

    private static final String NUMBERS =
            "a: Int, b: Int, c: Int, d: Int, hs: Set<Int>, xs: List<Int>";

    private static final String MEMBERSHIP = "Bool.not(Set.contains(a, hs))";

    /** The greatest {@code Int}, which {@code a + FIRST_SUM} reaches at {@code a == 10}. */
    private static final long FIRST_SUM = 9223372036854775797L;

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String THE_SUM_STOPPING =
            "a + " + FIRST_SUM + " - d >= 0 && " + MEMBERSHIP;

    private static final String THE_SUM_CANCELLING_TO_THE_FORM =
            "Int.floorMod(a + 9223372036854775807 - 9223372036854775807 - d, 7) >= 1";

    /**
     * Changing only the constant that puts the end where it is changes nothing: past the greatest
     * {@code Int} less ten, an end no guard-shaped reading took for the representation, and past
     * the greatest less three, one it did, the relation the stop turns on is read alike, and is
     * not shown reached at every value either way.
     */
    @Test
    void whereAStopFallsChangesNothingOfWhatIsRead() {
        String target = "Set.size(hs) == a";
        Map<String, List<String>> far = readingsOf(NUMBERS,
                "a + " + (Long.MAX_VALUE - 10) + " - a >= 0 && " + target);
        Map<String, List<String>> near = readingsOf(NUMBERS, "a + 3 - a >= 0 && " + target);
        assertEquals(far, near);
        assertEquals(List.of(NOT_SHOWN_REACHED), near.get("Set.size(hs)"), near::toString);
    }

    /**
     * The sum stops the run at {@code a} from 11 up: no class of the elements of {@code hs} starts
     * at 11 and no line is drawn there. The membership is not shown reached at every value of
     * {@code a}, which the stop keeps from 11 up, nor of the elements, which no run past the stop
     * holds beside an {@code a} equal to one from 11 up.
     */
    @Test
    void aMembershipTheStopTurnsOnIsDividedNowhereAndNotShownReached() {
        String firstStop = Long.toString(Long.MAX_VALUE - FIRST_SUM + 1);
        JsonNode report = reportOf(compiled(PARAMETERS, THE_SUM_STOPPING));
        Map<String, List<String>> readings = readingsIn(report);
        assertEquals(List.of(NOT_SHOWN_REACHED), readings.get("hs[*]"), readings::toString);
        assertTrue(readings.get("a").contains(NOT_SHOWN_REACHED), readings::toString);
        JsonNode partition = report.path("modules").get(0).path("behaviors").get(0)
                .path("partition");
        for (JsonNode axis : partition.path("axes")) {
            axis.path("classes").forEach(each ->
                    assertFalse(each.asString().contains(firstStop), each.asString()));
        }
        for (JsonNode border : partition.path("boundaries")) {
            assertFalse(border.path("value").asString().equals(firstStop), border.toString());
        }
    }

    /**
     * A stop on {@code a} bears on {@code b} where the way holds the two equal: the relation of
     * {@code b} past it is read as it is past the way alone, and is not shown reached at every
     * value of {@code b}.
     */
    @Test
    void aStopOnANumberTheWayHoldsAnotherToBearsOnTheOther() {
        String relation = "a == b && Set.size(hs) == b";
        Map<String, List<String>> past = readingsOf(NUMBERS,
                "a + " + (Long.MAX_VALUE - 10) + " - a >= 0 && " + relation);
        assertEquals(readingsOf(NUMBERS, relation).keySet(), past.keySet(), past::toString);
        assertEquals(List.of(NOT_SHOWN_REACHED), past.get("Set.size(hs)"), past::toString);
    }

    /**
     * A stop that keeps out values of a number between the ends of its run, and not the ends:
     * past {@code c + K} only a {@code c} of nought or one gets on, so of {@code a == 3 * b + c}
     * every third value of {@code a} up to 199 is reached by no run, and the run of {@code a}
     * from nought to 199 is as it was. The membership is not said reached at every value.
     */
    @Test
    void aStopThatThinsANumberOutWithoutMovingItsEndsBearsOnIt() {
        String condition = "a >= 0 && a <= 199 && b >= 0 && c >= 0 && c <= 2 && a == 3 * b + c"
                + " && c + 9223372036854775806 - c >= 0 && " + MEMBERSHIP;
        assertEquals(List.of(NOT_SHOWN), reasonsAt(NUMBERS, condition, "hs[*]"));
    }

    /**
     * A stop on a number a remainder ties to the one the relation reads keeps some classes of it
     * from every run, which no rule the region holds says: the membership is not said reached
     * at every value.
     */
    @Test
    void aStopOnANumberARemainderTiesToTheOneReadBearsOnIt() {
        String condition = "Int.floorMod(a - b, 20) == 0 && b >= 0 && b + "
                + (Long.MAX_VALUE - 10) + " - b >= 0 && " + MEMBERSHIP;
        assertEquals(List.of(NOT_SHOWN), reasonsAt(NUMBERS, condition, "hs[*]"));
    }

    /**
     * A choice whose left arm is a sum tying two numbers is worked out on every run, so
     * {@code a + K} stops every run past ten whichever arm is taken. A relation after it reads
     * the numbers as the model leaves them: {@code a} is one a run may stop before, and the line
     * at ten that the stop alone puts on {@code b} is drawn nowhere.
     */
    @Test
    void aRelationAfterASumThatTiesTwoNumbersIsReadWhereTheTypeEnds() {
        String choice = "(a + " + FIRST_SUM + " - d >= 0 || d > 0) && ";
        assertEquals(Map.of("a", List.of(NOT_SHOWN_REACHED, READ), "d", List.of(READ),
                        "b", List.of(NOT_SHOWN_REACHED)),
                readingsOf(NUMBERS, choice + "a - b > 0"));
        assertEquals(Map.of("a", List.of(NOT_SHOWN_REACHED, READ), "d", List.of(READ),
                        "hs[*]", List.of(NOT_SHOWN_REACHED)),
                readingsOf(NUMBERS, choice + MEMBERSHIP));
    }

    /**
     * A way with more choices on it than are looked along one by one is read again for the
     * relation, past what the run got past: the stop is where the representation stops there as
     * well, and the membership is read as it is on a way of no choices.
     */
    @Test
    void aWayReadAgainPastItsChoicesKeepsWhereTheRepresentationStops() {
        List<String> alternatives = new ArrayList<>();
        for (int b = 1; b <= CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum() + 1; b++) {
            alternatives.add("b == " + b);
        }
        String choice = "(" + String.join(" || ", alternatives) + ") && ";
        assertEquals(List.of(NOT_SHOWN_REACHED), reasonsAt(NUMBERS,
                choice + "a + " + FIRST_SUM + " - a >= 0 && " + MEMBERSHIP, "hs[*]"));
    }

    /**
     * An end over two numbers that moves the run of neither keeps out pairs of them: past
     * {@code a - d + K} no run holds {@code a - d} above ten. A relation over the pair is read as
     * the model leaves it, and where the end keeps every row from one of its sides, that nothing
     * arrives there is said.
     */
    @Test
    void anEndKeepingOutPairsAloneIsReadThroughTheRowsThatArrive() {
        String past = "a - d + " + FIRST_SUM + " >= 0 && ";
        assertEquals(readingsOf(NUMBERS, "a - d < -20"),
                readingsOf(NUMBERS, past + "a - d < -20"));
        List<String> cutOff = List.of(NOTHING_ARRIVES, READ);
        assertEquals(Map.of("a", cutOff, "d", cutOff), readingsOf(NUMBERS, past + "a - d > 20"));
    }

    /** A guard keeping {@code a} to ten is a statement of the model, and divides the elements. */
    @Test
    void aGuardAtTheValueTheSumStopsAtDividesTheElements() {
        assertEquals(List.of(), reasonsAt(PARAMETERS, "a <= 10 && " + MEMBERSHIP, "hs[*]"));
    }

    /**
     * A relation of each kind that reads the number a stop keeps values of says so, each read by
     * a reader of its own: a difference and a membership.
     */
    @Test
    void everyKindOfRelationReadingTheNumberSaysTheStop() {
        for (String target : List.of("a - b > 0", "Bool.not(Set.contains(a, hs))")) {
            Map<String, List<String>> readings = readingsOf(NUMBERS,
                    "a + " + FIRST_SUM + " - a >= 0 && " + target);
            assertTrue(readings.getOrDefault("a", List.of()).contains(NOT_SHOWN_REACHED),
                    () -> target + " " + readings);
        }
    }

    /** A relation over numbers the stop does not turn on is read as it is with nothing before it. */
    @Test
    void aRelationTheStopDoesNotTurnOnIsRead() {
        Map<String, List<String>> readings = readingsOf(NUMBERS,
                "a + " + FIRST_SUM + " - a >= 0 && b - c > 0");
        assertEquals(List.of(READ), readings.get("b"), readings::toString);
        assertEquals(List.of(READ), readings.get("c"), readings::toString);
    }

    /**
     * An end over a number the relation reads and one it does not, {@code a - d} within an
     * {@code Int} with {@code d} read, keeps no value of {@code d}: some {@code a} makes any
     * {@code d} get past it.
     */
    @Test
    void anEndTheNumbersTheRelationDoesNotReadMakeUpIsNoStop() {
        assertEquals(List.of(READ), reasonsAt(PARAMETERS,
                "Int.floorMod(a - d, 7) >= 1 && Bool.not(Set.contains(d, hs))", "hs[*]"));
    }

    /**
     * The values the sum stops on: {@code a} at 11 is past the greatest {@code Int} and at 10 is
     * the greatest, so a row the compiler offers for the rule is one the program gets past.
     */
    @Test
    void theRowsOfferedAreRunsThatGetPastTheSum() {
        assertThrows(ArithmeticException.class, () -> Math.addExact(11L, FIRST_SUM));
        assertEquals(Long.MAX_VALUE, Math.addExact(10L, FIRST_SUM));
        List<List<String>> rows = certifiedRowsOf(THE_SUM_STOPPING);
        assertFalse(rows.isEmpty());
        for (List<String> row : rows) {
            long a = Long.parseLong(row.get(0));
            assertDoesNotThrow(() -> Math.addExact(a, FIRST_SUM), row::toString);
        }
    }

    /**
     * The sum stops the same wherever it is written on the way: bound by a {@code let}, it is read
     * as written in place. Before a walk over a list, it stops on {@code a} and {@code d} and on no
     * element the walk reads, and the elements of the set are read as the membership reads them.
     */
    @Test
    void aSumStopsTheRunWhereverItIsWrittenOnTheWayToTheMembership() {
        String stop = "a + " + FIRST_SUM + " - d >= 0";
        assertEquals(readingsOf(PARAMETERS, THE_SUM_STOPPING), readingsOf(PARAMETERS,
                "{ let s = a + " + FIRST_SUM + " - d  s >= 0 && " + MEMBERSHIP + " }"));
        assertEquals(List.of(READ), reasonsAt(NUMBERS,
                stop + " && List.all(x -> Bool.not(Set.contains(x, hs)), xs)", "hs[*]"));
    }

    /**
     * The sum is worked out only on the runs where {@code d} is above nought, and the relation is
     * reached on the others without it. A run that works it out and stops is no run of the
     * relation, and which values that is the path does not say: it ties {@code a} and {@code d}
     * as the left arm of a choice does, and the relation is not shown reached at {@code a}.
     */
    @Test
    void aSumWorkedOutInAnArmTheMembershipIsReachedWithoutIsAStopTheMembershipIsNotShownPast() {
        Map<String, List<String>> readings = readingsOf(NUMBERS,
                "(d > 0 && a + " + FIRST_SUM + " - d >= 0) || a - b > 0");
        assertEquals(List.of(READ), readings.get("b"), readings::toString);
        assertEquals(List.of(NOT_SHOWN_REACHED), readings.get("a"), readings::toString);
    }

    /**
     * A stop inside a closure over a container the input holds is worked out only where the
     * container holds something, so a row holding it empty gets to the membership past no stop
     * beside any value of {@code a}. Where the membership is itself inside a closure over the
     * container, a row holding it empty gets to nothing, and {@code a} stays not shown.
     */
    @Test
    void aStopInAClosureOverAContainerIsAvoidedByAnEmptyContainerOnlyWhereTheMembershipDoesNotNeedIt() {
        String stop = "{ let s = List.map(x -> Int.floorMod(100, a - x - 1), xs)  ";
        String used = " || List.length(s) < 0 }";
        assertEquals(List.of(READ), reasonsAt(NUMBERS, stop + MEMBERSHIP + used, "a"));
        assertEquals(List.of(NOT_SHOWN_REACHED), reasonsAt(NUMBERS,
                stop + "List.any(x -> x >= 0 && " + MEMBERSHIP + ", xs)" + used, "a"));
        // A filter of the container holds something only where the container does, so a
        // closure over it is entered only there, though no position holds what it holds.
        assertEquals(List.of(READ), reasonsAt(NUMBERS,
                "{ let s = List.map(x -> Int.floorMod(100, a - x - 1),"
                        + " List.filter(x -> x > 0, xs))  " + MEMBERSHIP + used, "a"));
    }

    /**
     * The same sum as the left arm of a choice, worked out on every run before the membership,
     * stops runs on {@code a} and draws no line through the elements, which are not shown reached
     * at every value.
     */
    @Test
    void aSumTheLeftArmOfAChoiceWorksOutOnEveryRunIsAStopThere() {
        Map<String, List<String>> readings = readingsOf(PARAMETERS,
                "(a + " + FIRST_SUM + " - d >= 0 || d > 0) && " + MEMBERSHIP);
        assertEquals(List.of(NOT_SHOWN_REACHED), readings.get("hs[*]"), readings::toString);
        assertTrue(readings.get("a").contains(NOT_SHOWN_REACHED), readings::toString);
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
        Map<String, List<String>> readings = readingsOf(PARAMETERS, written);
        // The runs past the sum hold {@code a} at 10 or below, and the relation reaches each of
        // them, as it does under the guard; the elements of {@code hs} above 10 are never {@code a}.
        assertEquals(Map.of("a", List.of(READ), "hs[*]", List.of(NOT_SHOWN)), readings);
        assertEquals(readingsOf(PARAMETERS, "a <= 10 && " + written), readings);
        // And it is the comparison of the element with the sum, read the same written as one.
        assertEquals(readingsOf(PARAMETERS, "Bool.not(List.any(x -> x == a + " + FIRST_SUM + " - "
                + FIRST_SUM + ", Set.toList(hs)))"), readings);
    }

    /**
     * A comparison works out a sum, and where the sum is more than the form the comparison is
     * about, it stops a run at an {@code a} the form has a row at: {@code a + K - K == b} is
     * {@code a == b} to the form, and no run with {@code a} past 10 gets past the first sum. That
     * is the relation's own arithmetic, read as the guard that says the same is. A sum that is the
     * form itself stops where the form's own addends pass the type, and is read as the form.
     */
    @Test
    void aSumBeyondTheFormAComparisonIsAboutStopsARunAtALineOfTheModel() {
        String k = Long.toString(Long.MAX_VALUE - 10);
        String beyond = "a + K - K == b".replace("K", k);
        Map<String, List<String>> readings = readingsOf(NUMBERS, beyond);
        assertEquals(readingsOf(NUMBERS, "a <= 10 && " + beyond), readings);
        // No run with {@code a} past ten gets to the equality, so {@code b} past ten is never
        // equal to it: {@code b} is divided there and not left unanswered.
        assertFalse(readings.containsKey("b"), readings::toString);
        assertEquals(Map.of("a", List.of(READ), "b", List.of(READ)),
                readingsOf(NUMBERS, "a + K == b".replace("K", k)));
    }

    /**
     * Two programs read in one compilation whose statements are the same form: {@code a - d} and
     * {@code a + greatest - greatest - d} stop at different inputs, so what is proved of the one is
     * no proof of the other, whichever is asked first.
     */
    @Test
    void aFormAndASumThatCancelsToItShareNoProofInOneCompilation() {
        String plain = "Int.floorMod(a - d, 7) >= 1 && " + MEMBERSHIP;
        String cancelled = THE_SUM_CANCELLING_TO_THE_FORM + " && " + MEMBERSHIP;
        for (List<String> order : List.of(List.of("plain", "cancelled"),
                List.of("cancelled", "plain"))) {
            StringBuilder model = new StringBuilder("module demo\n");
            for (String behavior : order) {
                model.append("""

                        behavior NAME : (a: Int, d: Int, hs: Set<Int>) -> Bool
                        let NAME (a, d, hs) = CONDITION
                        """.replace("NAME", behavior).replace("CONDITION",
                        behavior.equals("plain") ? plain : cancelled));
            }
            Compilation compilation = Compilation.ofSource(model.toString(), "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            ACompiledModel.compiles(compilation);
            JsonNode report = reportOf(compilation);
            assertEquals(List.of(READ), reasonsOfBehavior(report, "plain", "hs[*]"), order::toString);
            // The sum stops at {@code a} from 1 up, which no statement of the form {@code a - d}
            // says: the membership after it is not shown reached, and is divided nowhere.
            assertEquals(List.of(NOT_SHOWN_REACHED),
                    reasonsOfBehavior(report, "cancelled", "hs[*]"), order::toString);
        }
    }

    /**
     * A remainder stops a run only where its divisor is nought, and a divisor is a number however it
     * is written: {@code 0} and {@code d - d} are nought on every run, so none reaches the
     * membership after them, and {@code 7} and {@code d - d + 7} are nought on none.
     */
    @Test
    void aRemainderByANoughtStopsEveryRunWhateverTheDivisorIsWrittenAs() {
        for (String divisor : List.of("0", "d - d")) {
            String condition = "{ let m = Int.floorMod(a, " + divisor + ")  " + MEMBERSHIP + " }";
            assertEquals(List.of(NOT_SHOWN_REACHED), reasonsAt(PARAMETERS, condition, "hs[*]"),
                    divisor);
        }
        for (String divisor : List.of("7", "d - d + 7")) {
            String condition = "{ let m = Int.floorMod(a, " + divisor + ")  " + MEMBERSHIP + " }";
            assertEquals(List.of(READ), reasonsAt(PARAMETERS, condition, "hs[*]"), divisor);
        }
    }

    /**
     * A divisor that comes to 7 is no divisor that is nought, but the sum that writes it stops at
     * {@code d} from 11 up: the membership of {@code d} is not shown reached at every value of it
     * or of the elements, which are divided nowhere, and a membership of {@code a}, which the sum
     * does not turn on, is read.
     */
    @Test
    void aDivisorThatComesToSevenStopsWhereTheSumThatWritesItDoes() {
        String divisor = "d + " + FIRST_SUM + " - d - " + FIRST_SUM + " + 7";
        String body = "{ let m = Int.floorMod(a, " + divisor + ")  Bool.not(Set.contains(%s, hs)) }";
        Map<String, List<String>> ofD = readingsOf(PARAMETERS, body.formatted("d"));
        assertEquals(List.of(NOT_SHOWN_REACHED), ofD.get("hs[*]"), ofD::toString);
        assertEquals(List.of(NOT_SHOWN_REACHED), ofD.get("d"), ofD::toString);
        assertEquals(List.of(READ), reasonsAt(PARAMETERS, body.formatted("a"), "hs[*]"));
    }

    /**
     * One body states {@code a - d} and a sum that cancels to it, on the way to one membership. The
     * statement of the form the sum cancels to is no proof for the sum, whichever is written first:
     * the sum stops where the form does not, and the membership is not shown reached.
     */
    @Test
    void aFormAndASumThatCancelsToItInOneBodyShareNoProof() {
        String plain = "Int.floorMod(a - d, 7) >= 1";
        for (String both : List.of(plain + " && " + THE_SUM_CANCELLING_TO_THE_FORM,
                THE_SUM_CANCELLING_TO_THE_FORM + " && " + plain)) {
            assertEquals(List.of(NOT_SHOWN),
                    reasonsAt(PARAMETERS, both + " && " + MEMBERSHIP, "hs[*]"), both);
        }
    }

    private static List<String> reasonsOfBehavior(JsonNode report, String behavior,
                                                  String position) {
        Set<String> found = new TreeSet<>();
        collectOfBehavior(report, behavior, position, found);
        return List.copyOf(found);
    }

    private static void collectOfBehavior(JsonNode node, String behavior, String position,
                                          Set<String> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason") && node.has("position")
                && node.path("ruleId").path("behavior").asString().equals(behavior)
                && node.path("position").asString().equals(position)) {
            out.add(node.path("reason").asString());
        }
        node.forEach(child -> collectOfBehavior(child, behavior, position, out));
    }

    /** What each position of {@code f} is said, a reason once, by position. */
    private static Map<String, List<String>> readingsOf(String parameters, String condition) {
        return readingsIn(reportOf(compiled(parameters, condition)));
    }

    /** What each position is said in {@code report}, a reason once, by position. */
    private static Map<String, List<String>> readingsIn(JsonNode report) {
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
        return ACompiledModel.compiles(compilation);
    }
}
