package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.msg.DeadBranchMessage;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An arm whose condition only values past where their type stops satisfy is one nothing reaches,
 * and it is that arm and not the other that is said to be.
 *
 * <p>Over the integers {@code b >= 1} and {@code a - b >= M}, with {@code M} the greatest
 * {@code Int}, have solutions, and none of them is an {@code Int}. A fork on that condition has its
 * {@code then} arm entered by no run; the same fork on the condition's negation has its
 * {@code else} arm entered by none. Which arm a report is about is read off the conditions it
 * points at: the ones that hold on the way to a {@code then} arm and the ones that fail on the way
 * to an {@code else} one.
 *
 * <p>Each condition is asked in both orders, since what a path knows must not depend on which half
 * was read first, and beside a neighbour that is reached, which says the answer is about the type's
 * end and not about the shape of the condition.
 */
class AWayOnlyValuesPastWhereTheirTypeStopsTakeIsReachedByNothingTest {

    private static final String MAX = "9223372036854775807";

    /** Which arm each report of a dead branch is about, in the order they were made. */
    private static List<String> armsSaidToBeDead(String condition) {
        String source = """
                module probe

                behavior m : (a: Int, b: Int) -> Bool
                let m (a, b) =
                    if %s
                    then true
                    else false
                """.formatted(condition);
        List<String> out = new ArrayList<>();
        for (Diagnostic each : Compiler.compileWithWarnings(source).warnings()) {
            if (each.code().equals("E1327")) {
                out.add(armOf(each));
            }
        }
        return out;
    }

    private static String armOf(Diagnostic report) {
        boolean holds = report.secondary().stream().map(LabeledRegion::said)
                .anyMatch(DeadBranchMessage.ThisOneHoldsOnTheWayHere.class::isInstance);
        boolean fails = report.secondary().stream().map(LabeledRegion::said)
                .anyMatch(DeadBranchMessage.ThisOneFailsOnTheWayHere.class::isInstance);
        return holds && !fails ? "then" : fails && !holds ? "else" : "unclear";
    }

    private static Map<String, List<String>> asked(String... conditions) {
        Map<String, List<String>> out = new TreeMap<>();
        for (String each : conditions) {
            out.put(each, armsSaidToBeDead(each));
        }
        return out;
    }

    private static Map<String, List<String>> all(List<String> answer, String... conditions) {
        Map<String, List<String>> out = new TreeMap<>();
        for (String each : conditions) {
            out.put(each, answer);
        }
        return out;
    }

    @Test
    void aSumPastTheGreatestIntMakesTheThenArmDeadWhicheverHalfIsReadFirst() {
        String[] past = {
            "b >= 1 && a - b >= " + MAX,
            "a - b >= " + MAX + " && b >= 1"};
        assertEquals(all(List.of("then"), past), asked(past));
    }

    @Test
    void aSumPastTheLeastIntMakesTheThenArmDead() {
        String[] past = {
            "b >= 1 && a + b < 0 - " + MAX,
            "a + b < 0 - " + MAX + " && b >= 1"};
        assertEquals(all(List.of("then"), past), asked(past));
    }

    @Test
    void theNegationOfSuchAConditionMakesTheElseArmDeadAndNotTheThenArm() {
        String[] past = {
            "b < 1 || a - b < " + MAX,
            "a - b < " + MAX + " || b < 1"};
        assertEquals(all(List.of("else"), past), asked(past));
    }

    @Test
    void theNeighboursThatStayInsideTheTypeAreReachedOnBothArms() {
        String[] inside = {
            "b >= 1 && a - b >= 9223372036854775806",
            "b >= 0 && a - b >= " + MAX,
            "b < 1 || a - b < 9223372036854775806",
            "b >= 1 && a + b < 0 - 9223372036854775807 + 1"};
        assertEquals(all(List.of(), inside), asked(inside));
    }
}
