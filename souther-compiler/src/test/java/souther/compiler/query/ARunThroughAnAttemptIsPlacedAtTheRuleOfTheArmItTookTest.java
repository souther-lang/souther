package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Citation;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.OnTheWay;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A row through an attempted construction is placed at the rule of the arm it took.
 *
 * <p>The success and each departure of an attempt are distinctions of the decision a body states,
 * and a run through one is recorded at that arm. So each rule goes through one arm, a run matches
 * the rule of the arm it went through and no other, and a body with an attempt in it is measured the
 * way one written with a {@code guard} is.
 */
class ARunThroughAnAttemptIsPlacedAtTheRuleOfTheArmItTookTest {

    /** The success branch holds a comparison of its own, and the departure holds none. */
    private static final String SIZE = """
            module demo
            data Q = Int
                invariant value >= 0
            data Nope
            data Big
            data Small
            behavior size : (x: Int) -> Big | Small | Nope
                constructs Q
            let size (x) = if Q(x) as q then (if q.value > 10 then Big else Small) else Nope
            example size
                | (11) -> Big
                | (10) -> Small
                | (-1) -> Nope
            """;

    /** Two departures, one per clause, and nothing under the success branch. */
    private static final String CHECK = """
            module demo
            data R = Int
                invariant low = value >= 0
                invariant high = value <= 100
            data Low
            data High
            data Fine
            behavior check : (x: Int) -> Fine | Low | High
                constructs R
            let check (x) = if R(x) as r then Fine else
                | low -> Low
                | high -> High
            example check
                | (5) -> Fine
                | (-1) -> Low
                | (101) -> High
            """;

    @Test
    void eachRowIsPlacedAtTheRuleThroughTheArmItTook() {
        assertEveryRowIsPlacedAtItsOwnRule(SIZE, "size");
    }

    @Test
    void eachDepartureIsARuleOfItsOwn() {
        assertEveryRowIsPlacedAtItsOwnRule(CHECK, "check");
    }

    /**
     * What a way declines at an attempt's arm is sent to where that arm is written.
     *
     * <p>The arm is a condition the source wrote, so the module that wrote it is what places it. A
     * report about a row composed without it asks there, and a place nothing filed is a report with
     * nowhere to send its reader.
     */
    @Test
    void theArmsAWayDeclinesAreSentToWhereTheyAreWritten() {
        Compilation compilation = compiled(CHECK);
        DecisionEvidence evidence = evidenceOf(compilation, "check");
        Set<Citation> sentTo = new LinkedHashSet<>();
        for (DecisionReading.Ruled ruled : evidence.read().found()) {
            for (OnTheWay.Declined declined : ruled.states().declined()) {
                Citation at = Sites.placeIfKnown(compilation.db(), declined.anchor());
                assertInstanceOf(Citation.Written.class, at,
                        () -> "an arm the source wrote is placed where it is written: " + declined);
                sentTo.add(at);
            }
        }
        assertEquals(3, sentTo.size(),
                () -> "the success and the two departures are three places: " + sentTo);
    }

    /**
     * Three rules and three rows, each row at a rule of its own.
     *
     * <p>The rows are placed, the rules they were placed at are every rule the body has, and no
     * rule is left untaken. A body whose arms were read as no condition at all fails the first of
     * these: its departure is a rule every run matches, and no row is placed.
     */
    private static void assertEveryRowIsPlacedAtItsOwnRule(String model, String behavior) {
        DecisionEvidence evidence = evidenceOf(model, behavior);
        List<DecisionRule> rules = evidence.rules();
        assertEquals(3, rules.size(), () -> "one rule per way through the body: " + rules);
        DecisionEvidence.RowsPlaced placed = evidence.took().made()
                .orElseThrow(() -> new AssertionError("the rows were read: " + evidence.took()));
        assertEquals(3, placed.rowsPlaced(), () -> "every row is placed at a rule: " + placed);
        assertEquals(Set.copyOf(rules), placed.rules(),
                () -> "and the three are placed at the three rules: " + placed);
        assertEquals(List.of(), evidence.notTakenByRows(),
                () -> "so no rule is left that no row took: " + placed);
    }

    private static DecisionEvidence evidenceOf(String model, String behavior) {
        return evidenceOf(compiled(model), behavior);
    }

    private static DecisionEvidence evidenceOf(Compilation compilation, String behavior) {
        return compilation.db().ask(new Adequacy.Decides(compilation.modules().get(0))).value()
                .get(behavior);
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
