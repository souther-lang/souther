package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.ReadingGap;

import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A budget of this compiler's may leave an obligation undecided and may never take it out of the
 * count.
 *
 * <p>What the account is for is telling an author what the model owes. A row the rows do not answer
 * and nothing shows can be written is left out of it, because asking for a row that may not exist
 * is asking for work nobody can do — and that is a statement about the model. A row this compiler
 * composed and could not read back is not: the value went through the module's own decoders, and
 * what is missing is the reading. Counted the same way, the numbers a report prints move with how
 * much of a value an observation happens to keep.
 *
 * <p>Put to the fold directly and not through a model. Reaching every row of the table from source
 * takes a model per row, and the one for a point whose showing was stopped takes a value of about
 * two thousand nodes — which is minutes of composing to establish one arm of a switch. The models
 * that are cheap are elsewhere; what is held here is the rule they are read by.
 */
class ALimitOfThisCompilerDoesNotTakeAnObligationOutOfTheCountTest {

    /**
     * A point the rows ran out on, where the value built for it could not be read back.
     *
     * <p>The row the table exists for. Nothing has shown the point writable — the reading that
     * would have is the one that did not come back — and the obligation stays counted all the same,
     * because what stopped the showing is this compiler's own budget and not the model refusing a
     * row.
     */
    @Test
    void aShowingStoppedByALimitLeavesTheObligationCountedAndUndecided() {
        ObligationDisposition disposition =
                ObligationDisposition.of(new ObligationCoverage.Missed(), prevented());

        assertInstanceOf(ObligationDisposition.Counted.class, disposition,
                "a point whose showing a limit stopped is one the model still owes a row at");
        assertEquals(new ObligationDisposition.Undecided(
                        EnumSet.of(ObligationDisposition.Uncertainty.WRITABILITY)),
                disposition,
                "and the question left open is whether a row can be written, not whether one is");
    }

    /**
     * The same coverage with nothing behind it at all, which is the row beside it.
     *
     * <p>The pair is the measurement. Both are points every row was read against and none is at;
     * they differ in whether anything was stopped from showing a row could be written there. Held
     * on one of them alone, a fold that ignored the difference would pass.
     */
    @Test
    void aShowingNothingEverMadeLeavesTheObligationOutOfTheCount() {
        ObligationDisposition disposition = ObligationDisposition.of(
                new ObligationCoverage.Missed(), new WritabilityKnowledge.NoEvidence());

        assertEquals(new ObligationDisposition.NotCounted(
                        Set.of(ObligationDisposition.Reason.NOT_KNOWN_TO_BE_WRITABLE)),
                disposition,
                "a point nothing promises a row at is not one an author is behind on");
    }

    /** And the same coverage where something did show it, which is the only finding of the three. */
    @Test
    void aShowingThatArrivedIsTheOneThatMakesAFinding() {
        assertEquals(new ObligationDisposition.Unmet(),
                ObligationDisposition.of(new ObligationCoverage.Missed(), established()),
                "a point the rules prove and no row is at is a row somebody owes");
    }

    /**
     * Both questions open at one point are both said.
     *
     * <p>A reading that stopped short and a showing that was stopped are about different things,
     * and either one alone is a choice of which to tell.
     */
    @Test
    void twoOpenQuestionsAtOnePointAreBothSaid() {
        ObligationDisposition disposition = ObligationDisposition.of(
                new ObligationCoverage.Undecided(WeakeningSet.of(
                        new Weakening.BorderValueUnreadable(null,
                                ReadingGap.of(Incompleteness.Code.VALUE_TRUNCATED)))),
                prevented());

        assertEquals(new ObligationDisposition.Undecided(EnumSet.of(
                        ObligationDisposition.Uncertainty.COVERAGE,
                        ObligationDisposition.Uncertainty.WRITABILITY)),
                disposition,
                "the rows left one question open and the search left the other");
    }

    /**
     * A point nothing was read against keeps both reasons it is out of the count.
     *
     * <p>They are independent facts about the point and a reader is owed both: one says there was
     * nothing to find, the other says nothing promises there is anything to find.
     */
    @Test
    void aPointNothingWasReadAgainstKeepsEveryReasonItIsOut() {
        ObligationDisposition disposition = ObligationDisposition.of(
                new ObligationCoverage.NotMeasured(ItemAssessment.Coverage.NotAsked.NO_ROWS),
                new WritabilityKnowledge.NoEvidence());

        assertEquals(new ObligationDisposition.NotCounted(Set.of(
                        ObligationDisposition.Reason.NOTHING_WAS_READ,
                        ObligationDisposition.Reason.NOT_KNOWN_TO_BE_WRITABLE)),
                disposition,
                "nothing was read and nothing promises a row, and both are true of it");
    }

    /**
     * Tightening what an observation keeps may weaken what is known and may not empty the count.
     *
     * <p>The law the table is for, said over the states rather than over one pair. A budget of this
     * compiler's turns what was established into what was prevented; every disposition that was
     * counted under the first is counted under the second.
     */
    @Test
    void everyObligationCountedWithGroundsIsStillCountedWhenALimitStopsThem() {
        for (ObligationCoverage coverage : everyCoverage()) {
            ObligationDisposition withGrounds = ObligationDisposition.of(coverage, established());
            if (!(withGrounds instanceof ObligationDisposition.Counted)) {
                continue;
            }
            assertInstanceOf(ObligationDisposition.Counted.class,
                    ObligationDisposition.of(coverage, prevented()),
                    () -> "a limit took " + coverage + " out of the count");
        }
    }

    /**
     * And it may not turn one verdict into the other, which is what a resource policy cannot say.
     *
     * <p>What a limit may do is take knowledge away, and the states are ordered by how much they
     * claim: a row is there, no row is there, nobody can say. Moving along that order downwards is
     * a limit doing its job; moving across it — a miss becoming a hit, or either becoming a point
     * the account no longer holds — is the policy answering a question about the model.
     */
    @Test
    void aLimitDoesNotTurnAMissIntoAHitOrBack() {
        for (ObligationCoverage coverage : everyCoverage()) {
            ObligationDisposition withGrounds = ObligationDisposition.of(coverage, established());
            ObligationDisposition stopped = ObligationDisposition.of(coverage, prevented());
            assertTrue(weakensTo(withGrounds, stopped),
                    () -> "a limit moved " + coverage + " from " + withGrounds + " to " + stopped
                            + ", which is a verdict and not a loss of knowledge");
        }
    }

    /**
     * Whether {@code after} claims no more than {@code before}.
     *
     * <p>A verdict may stand or become the one that claims nothing; a point already outside the
     * count stays outside it, and may be outside it for more reasons than before, since a reason is
     * something known about the point rather than a claim about the model.
     */
    private static boolean weakensTo(ObligationDisposition before, ObligationDisposition after) {
        return switch (before) {
            case ObligationDisposition.Met _, ObligationDisposition.Unmet _ ->
                    after.equals(before) || after instanceof ObligationDisposition.Undecided;
            case ObligationDisposition.Undecided it ->
                    after instanceof ObligationDisposition.Undecided then
                            && then.because().containsAll(it.because());
            case ObligationDisposition.NotCounted it ->
                    after instanceof ObligationDisposition.NotCounted then
                            && then.because().containsAll(it.because());
        };
    }

    private static List<ObligationCoverage> everyCoverage() {
        return List.of(new ObligationCoverage.Witnessed(),
                new ObligationCoverage.Missed(),
                new ObligationCoverage.Undecided(WeakeningSet.of(
                        new Weakening.BorderValueUnreadable(null,
                                ReadingGap.of(Incompleteness.Code.VALUE_TRUNCATED)))),
                new ObligationCoverage.NotMeasured(ItemAssessment.Coverage.NotAsked.NO_ROWS));
    }

    private static WritabilityKnowledge established() {
        return new WritabilityKnowledge.Established(new ItemAssessment.WritabilityEvidence(
                Set.of(ItemAssessment.WritabilityEvidence.Ground.THE_RULES_PROVE_IT)));
    }

    private static WritabilityKnowledge prevented() {
        return new WritabilityKnowledge.Prevented(new EstablishmentGap.Observation(
                EnumSet.of(Incompleteness.Code.VALUE_TRUNCATED)));
    }
}
