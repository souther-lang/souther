package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.diag.CompileException;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Proof;
import souther.compiler.reach.Reachability;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A fork's binding is what the guards inside it read against, and every fork that has one hands it
 * over the same way.
 *
 * <p>Four things a walk over a body has to get right, each of which a reading that only handled the
 * shapes it happened to meet got wrong: a body with nothing to measure is still a body with places
 * in it, an arm that binds nothing binds nothing, an attempted construction's success branch
 * carries what it built, and a condition nothing could read is not a reason for anything.
 */
class EveryForkIsReadUnderWhatItsBindingCarriesTest {

    private static List<Reachability> armsOf(String source, String module, String behavior) {
        Compilation c = Compilation.ofSource(source, module);
        Map<String, PathReachability.Answers> byBehavior =
                c.db().ask(new Adequacy.PathReached(module)).value();
        return byBehavior == null || byBehavior.get(behavior) == null ? List.of()
                : byBehavior.get(behavior).found().entrySet().stream()
                        .filter(each -> each.getKey() instanceof ControlPointId.ArmOccurrence)
                        .map(Map.Entry::getValue)
                        .toList();
    }

    private static List<Proof> provenIn(String source, String module, String behavior) {
        return armsOf(source, module, behavior).stream()
                .filter(Reachability.Unreachable.class::isInstance)
                .map(each -> ((Reachability.Unreachable) each).proof())
                .toList();
    }

    /**
     * A body every arm of which answers {@code unreachable} has no site a run could be recorded at,
     * and has arms all the same.
     *
     * <p>A reading that asked whether there was anything to measure, and stopped where there was
     * not, skipped exactly the bodies a claim is made in — which is what naming the places apart
     * from the probes was for.
     */
    @Test
    void aBodyWithNothingToMeasureIsStillABodyWithPlacesInIt() {
        CompileException refused = assertThrows(CompileException.class, () ->
                Compiler.compileWithWarnings("""
                        module demo

                        data On
                        data Off
                        data Flag = On | Off
                        data Answer = Int

                        behavior pick : (f: Flag) -> Answer

                        let pick (f) = match f with
                            | On  -> unreachable "On never arrives"
                            | Off -> unreachable "Off never arrives"
                        """),
                "both cases arrive, and nothing here can be recorded to say otherwise");
        assertEquals("E1326", refused.diagnostic().code());
    }

    /**
     * An arm binding nothing introduces nothing, and the walk goes on inside it.
     *
     * <p>Handing a case's binding over without asking whether it has one falls over on every
     * ordinary unit case, and the walk that falls over answers about what it had reached — so a
     * dead guard under such an arm is one nothing proves.
     */
    @Test
    void anArmThatBindsNothingIsStillWalkedInto() {
        assertEquals(1, provenIn("""
                module demo

                data On
                data Off
                data Flag = On | Off
                data Amount = Int invariant value >= 0 && value <= 100
                data Free
                data Charged = { yen: Int }

                behavior pick : (f: Flag, a: Amount) -> Free | Charged
                    constructs Free, Charged

                let pick (f, a) = match f with
                    | On -> {
                        guard a.value < 10 else Free
                        guard a.value < 20 else Free
                        Charged { yen = 1 }
                    }
                    | Off -> Free
                """, "demo", "pick").size(),
                "the second guard under a unit arm is one nothing reaches");
    }

    /**
     * An attempted construction's success branch carries what the type it built guarantees.
     *
     * <p>Which is the whole of what a guard inside that branch reads against: without it the
     * binding is a value nothing is known of, and a guard the invariant rules out is one nothing
     * proves.
     */
    @Test
    void aSuccessfulAttemptHandsOverWhatItBuilt() {
        assertEquals(1, provenIn("""
                module demo

                data Amount = Int invariant value >= 0 && value <= 100
                data Free
                data Charged = { yen: Int }

                behavior pick : (raw: Int) -> Free | Charged
                    constructs Free, Charged, Amount

                let pick (raw) = if Amount(raw) as a then {
                        guard a.value < 200 else Free
                        Charged { yen = 1 }
                    } else Free
                """, "demo", "pick").size(),
                "an `Amount` stops at a hundred, so nothing that was built departs at two hundred");
    }

    /**
     * A condition the reading could not take in is not among the reasons a proof gives.
     *
     * <p>The proof says which conditions leave nothing together. One that narrowed nothing did no
     * part of that, and naming it says a line was holding where nothing here could tell whether it
     * was.
     */
    @Test
    void aConditionNothingCouldReadIsNotAReasonForAnything() {
        List<Proof> proven = provenIn("""
                module demo

                data Amount = Int invariant value >= 0 && value <= 100
                data Free
                data Charged = { yen: Int }

                behavior pick : (a: Amount, xs: List<Int>) -> Free | Charged
                    constructs Free, Charged

                let pick (a, xs) = {
                    guard List.length(List.filter(x -> x > 0, xs)) >= 1 else Free
                    guard a.value < 200 else Free
                    Charged { yen = 1 }
                }
                """, "demo", "pick");
        assertEquals(1, proven.size(), "the numeric guard departs where an `Amount` cannot go");
        List<PathDecision> why = ((Proof.ConflictingPathConditions) proven.get(0)).decisions();
        assertEquals(1, why.size(),
                () -> "only the condition that was read is a reason: " + why);
    }
}
