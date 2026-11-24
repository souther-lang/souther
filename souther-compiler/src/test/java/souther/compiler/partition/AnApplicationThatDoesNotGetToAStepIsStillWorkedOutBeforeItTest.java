package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run has worked out by one application of a closure, and what it is handed, is every
 * application before it, whether or not that one gets to the step being judged: an application
 * taking another arm is worked out all the same, and hands on what it answered. An application
 * made only on some rows is not taken as made.
 */
class AnApplicationThatDoesNotGetToAStepIsStillWorkedOutBeforeItTest {

    /** One model for every case, compiled once. */
    private static final Compilation COMPILED = ACompiledModel.measured("""
                module demo

                data In = { p: Int, q: Int }

                behavior folded : (i: In) -> Int
                let folded (i) = List.fold((a, x) -> if x == 0 then i.q else a + 1, 0, [0, 1])

                behavior mapped : (i: In) -> Int
                let mapped (i) = List.length(List.map(x -> if x == 0 then
                    Rational.toInt(DOWN, 4 / i.p) else x + i.q, [0, 1]))

                behavior filtered : (i: In) -> Int
                let filtered (i) = List.fold((a, x) -> if x == 0 then 0 else a + 1,
                    9223372036854775807, List.filter(x -> x /= i.p, [0, 1]))

                behavior seeded : (i: In) -> Int
                let seeded (i) = List.fold((a, x) -> if a * a == 0 then x + 1 else 0, 0,
                    [1, i.q])
                """, new Adequacy.Asked(Adequacy.Level.OFF, false));

    private static List<StopAssessment.Judgement> judged(String behavior) {
        return SitesJudged.of(COMPILED, behavior);
    }

    private static NumericTerm valueOf(String field) {
        return new NumericTerm.ValueOf(TermPath.of("i").then(field));
    }

    private static final ExactRatio GREATEST = ExactRatio.of(Long.MAX_VALUE);

    /** The first application takes the other arm and answers {@code i.q}, which the second is
     *  handed: its sum stops at the greatest {@code i.q}, and is not read as one over the seed. */
    @Test
    void aFoldHandsOnWhatAnApplicationThatTookTheOtherArmAnswered() {
        List<StopAssessment.Judgement> judged = judged("folded");
        assertTrue(judged.stream().anyMatch(one -> one instanceof StopAssessment.Judgement.Stops(
                var shown) && GREATEST.equals(shown.at().get(valueOf("q")))), judged::toString);
    }

    /** The first application divides by {@code i.p} on its arm, before the second gets to its
     *  sum: no value is shown to stop at the sum that stops at the division first. */
    @Test
    void anApplicationBeforeTheStepOnAnotherArmIsGotPastFirst() {
        List<StopAssessment.Judgement> judged = judged("mapped");
        assertFalse(judged.stream().anyMatch(one -> one instanceof StopAssessment.Judgement.Stops(
                var shown) && shown.site() instanceof StopAssessment.Site.PastItsEnds
                && ExactRatio.ZERO.equals(shown.at().get(valueOf("p")))), judged::toString);
    }

    /** The first application answers two, so the second takes the other arm and never works
     *  {@code x + 1} out over {@code i.q}: whether a run gets to the sum on an application is
     *  read with what that application is handed, and no run is shown to stop. */
    @Test
    void whetherARunGetsToAStepIsReadWithWhatTheApplicationIsHanded() {
        List<StopAssessment.Judgement> judged = judged("seeded");
        assertTrue(judged.stream().noneMatch(StopAssessment.Judgement.Stops.class::isInstance),
                judged::toString);
    }

    /** The first application is made only where {@code i.p} is not nought: where it is, the
     *  second is handed the seed, and its sum, the one step that may stop, stops. What the first
     *  answers is not read as what the second is handed, so the sum is not shown to get past. */
    @Test
    void anApplicationMadeOnlyOnSomeRowsHandsOnNothingTakenAsMade() {
        List<StopAssessment.Judgement> judged = judged("filtered");
        assertFalse(judged.isEmpty(), judged::toString);
        assertTrue(judged.stream().noneMatch(StopAssessment.Judgement.Safe.class::isInstance),
                judged::toString);
    }
}
