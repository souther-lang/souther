package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reach.Proof;
import souther.compiler.reach.Reachability;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard whose departure the guards above it have already ruled out is proven unreachable.
 *
 * <p>The reading this asks was already being made — the invariant-discharge check threads the same
 * conditions and stops at a place they cannot all hold — and it stopped there rather than saying so,
 * while every measure derived the same question again from the declarations alone. Nothing arrives
 * at {@code a.value >= 6000} when everything that got this far is under 5000, and the declarations
 * cannot see that: they say only that an {@code Amount} runs from 0 to a million.
 *
 * <p>The second guard is what the first one leaves, so this is measured against the first: one
 * model, two departures, and only the second of them is proven. A model where nothing is proven
 * would pass a reading that proves everything, and a model where everything is would pass one that
 * proves nothing.
 */
class AGuardTheGuardsAboveItRuleOutIsProvenTest {

    private static final String TWO_GUARDS = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }

            behavior charge : (a: Amount) -> Free | Charged
                constructs Free, Charged

            let charge (a) = {
                guard a.value < 5000 else Free
                guard a.value < 6000 else Free
                Charged { yen = 500 }
            }
            """;

    /** The same, with a second guard the first one does not settle. */
    private static final String TWO_LIVE_GUARDS = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }

            behavior charge : (a: Amount) -> Free | Charged
                constructs Free, Charged

            let charge (a) = {
                guard a.value < 5000 else Free
                guard a.value > 100 else Free
                Charged { yen = 500 }
            }
            """;

    /** A guard whose departure is outside what the declaration admits at all. */
    private static final String OUTSIDE_THE_DECLARATION = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }

            behavior charge : (a: Amount) -> Free | Charged
                constructs Free, Charged

            let charge (a) = {
                guard a.value < 2000000 else Free
                Charged { yen = 500 }
            }
            """;

    /**
     * What was said about every arm of {@code charge}.
     *
     * <p>Read as a collection and not by position. The walk numbers an inner fork while it is
     * inside the arm that holds it, so which index a departure lands on is a fact about the
     * traversal; what is being measured is which arms are proven, and that is the same however
     * they are ordered.
     */
    private static List<Reachability> armsOf(String source) {
        Compilation c = Compilation.ofSource(source, "d");
        Map<String, PathReachability.Answers> byBehavior =
                c.db().ask(new Adequacy.PathReached("d")).value();
        assertTrue(byBehavior != null && byBehavior.containsKey("charge"),
                "the module answers nothing about `charge`");
        return byBehavior.get("charge").found().entrySet().stream()
                .filter(each -> each.getKey() instanceof ControlPointId.ArmOccurrence)
                .map(Map.Entry::getValue)
                .toList();
    }

    private static List<Proof> provenIn(String source) {
        return armsOf(source).stream()
                .filter(Reachability.Unreachable.class::isInstance)
                .map(each -> ((Reachability.Unreachable) each).proof())
                .toList();
    }

    @Test
    void aDepartureNothingCanTakeIsProvenAndNothingElseIs() {
        assertEquals(4, armsOf(TWO_GUARDS).size(), "two guards make two forks of two arms");
        List<Proof> proven = provenIn(TWO_GUARDS);
        assertEquals(1, proven.size(),
                "the second guard's departure, and not the first's and neither of the arms it "
                        + "guards");
        Proof why = proven.get(0);
        assertInstanceOf(Proof.ConflictingPathConditions.class, why,
                "what makes it unreachable is the conditions on the way to it");
        assertEquals(2, ((Proof.ConflictingPathConditions) why).decisions().size(),
                "both guards are on the way to it, and the proof says which they are");
    }

    @Test
    void aSecondGuardTheFirstDoesNotSettleIsLeftAsItIs() {
        assertEquals(4, armsOf(TWO_LIVE_GUARDS).size());
        assertEquals(List.of(), provenIn(TWO_LIVE_GUARDS),
                "a value between 100 and 5000 takes neither departure, and one under 100 takes the "
                        + "second — so nothing here is an arm nothing reaches");
    }

    @Test
    void aDepartureOutsideWhatTheDeclarationAdmitsIsProvenToo() {
        assertEquals(2, armsOf(OUTSIDE_THE_DECLARATION).size(),
                "one guard makes one fork of two arms");
        List<Proof> proven = provenIn(OUTSIDE_THE_DECLARATION);
        assertEquals(1, proven.size(), "an `Amount` stops at a million, so nothing reaches two");
        assertEquals(1, ((Proof.ConflictingPathConditions) proven.get(0)).decisions().size(),
                "one guard is on the way to it; what it conflicts with is what the input is");
    }

    @Test
    void nothingIsProvenReachable() {
        // Every route to `Reachable` is about the program — a run that went through, a rule that
        // settles it completely, a value put together — and this reading reads none of them. A
        // state the domains found no contradiction in is a state they had nothing to say about.
        for (String source : List.of(TWO_GUARDS, TWO_LIVE_GUARDS, OUTSIDE_THE_DECLARATION)) {
            for (Reachability each : armsOf(source)) {
                assertTrue(!(each instanceof Reachability.Reachable),
                        "this reading proves nothing arrives, never that something does");
            }
        }
    }
}
