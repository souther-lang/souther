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
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
     * A row that went through an arm this reading had proven nothing reaches is not warned about.
     *
     * <p>What happened happened: the proof was wrong rather than the row, and the arm is back in
     * every denominator before any measure sees it. A diagnostic reading the proof instead would be
     * the one consumer left telling an author about a branch the rows have already been through.
     *
     * <p>The row lands on the arm by way of a fake that answers what no `Amount` could — which is
     * how a run gets somewhere the rules say nothing arrives.
     */
    @Test
    void aRowThroughAnArmTheProofRuledOutIsNotWarnedAbout() {
        String model = """
                module demo

                data Amount = Int invariant value >= 0 && value <= 100
                data Free
                data Charged = { yen: Int }

                behavior charge : (a: Amount) -> Free | Charged
                    constructs Free, Charged

                let charge (a) = {
                    guard a.value < 200 else Free
                    Charged { yen = 1 }
                }
                """;
        Compilation c = Compilation.ofSource(model, "demo");
        c.measure(Adequacy.Asked.reportOnly());
        c.answerEverything();
        List<String> codes = c.reports().stream()
                .map(each -> each.report().diagnostic().code())
                .filter("E1327"::equals)
                .toList();
        assertEquals(List.of("E1327"), codes,
                "nothing ran through it, so what the reading proved stands");

        // And it is the answer with the rows in it that the diagnostic asked for. A row cannot be
        // written through an arm nothing reaches, so no model puts the two readings apart on its
        // own — what can be measured is which of them the question was put to, and asking this one
        // is what makes a run through such an arm take the warning away.
        assertTrue(c.db().isComputed(new Adequacy.Arrived("demo")),
                "the diagnostic reads what arrives once the rows have run");

        // What that answer does with a run, at the value it is made of.
        PathReachability.Answers answers =
                c.db().ask(new Adequacy.PathReached("demo")).value().get("charge");
        int probe = answers.found().entrySet().stream()
                .filter(each -> each.getValue() instanceof Reachability.Unreachable)
                .filter(each -> each.getKey() instanceof ControlPointId.ArmOccurrence)
                .map(each -> (ControlPointId.ArmOccurrence) each.getKey())
                .findFirst().orElseThrow().probe().orElseThrow();
        PathReachability.Answers.AsRun ran = answers.asRunWith(Set.of(probe));
        assertEquals(Set.of(probe), ran.provedWrong(),
                "a row through it is what takes the proof back");
        assertEquals(List.of(), ran.answers().found().entrySet().stream()
                        .filter(each -> each.getKey() instanceof ControlPointId.ArmOccurrence)
                        .map(Map.Entry::getValue)
                        .filter(Reachability.Unreachable.class::isInstance).toList(),
                "so no arm is left for the diagnostic to be about");
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
                    guard a.value < 50 else Free
                    guard a.value < 80 else Free
                    Charged { yen = 1 }
                }
                """, "demo", "pick");
        assertEquals(1, proven.size(),
                "nothing under fifty is eighty or more, and the guard above is what says so");
        List<PathDecision> why = WhatAnAnswerSays.conditionsIn(proven.get(0));
        assertEquals(2, why.size(),
                () -> "the two guards that were read, and not the one through a fold: " + why);
    }
}
