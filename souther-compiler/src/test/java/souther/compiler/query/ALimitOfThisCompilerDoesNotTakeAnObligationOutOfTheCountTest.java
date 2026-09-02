package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.ReadingGap;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A limit of this compiler's may leave an obligation undecided and may never take it out of the
 * count.
 *
 * <p>What the account is for is telling an author what the model owes. Whether a row is owed at a
 * point is settled by the rules — a border that owes no row says so with a reason read off them
 * ({@link souther.compiler.partition.NotOwedReason}) — and nothing this compiler managed or failed
 * to do reaches that decision. So what is left for this fold to say is what is known about a point
 * that is owed, and none of its answers is "no longer owed".
 *
 * <p>It was not so for one pair. A point every row was read against and none was at, with nothing
 * to show a row could be written there, was dropped from the account — on the reading that asking
 * for a row nothing promises is asking for work nobody can do. What is composed for a point is
 * composed out of the whole value it sits in, so one rule this compiler could not read anywhere
 * under a parameter emptied the grounds for every point beneath it, and a field nobody could build
 * a value for took its siblings' obligations out of the denominator with it (issue #1249). The
 * corpus that was measured on holds no obligation dropped for a reason the model gave: every one of
 * them was a value this compiler could not compose or could not read back.
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
     * <p>Nothing has shown the point writable — the reading that would have is the one that did not
     * come back — and the obligation stands, because what stopped the showing is this compiler's own
     * budget and not the model refusing a row.
     */
    @Test
    void aShowingStoppedByALimitLeavesTheObligationUndecided() {
        assertEquals(ObligationDisposition.Undecided.about(List.of(
                        new ObligationDisposition.Uncertainty.WhetherARowCanBeWritten.Stopped(
                                prevented()))),
                ObligationDisposition.of(new ObligationCoverage.Missed(), prevented()),
                "the question left open is whether a row can be written, not whether one is,"
                        + " and it says what stopped the showing");
    }

    /**
     * The same coverage with nothing behind it at all, which is the row beside it.
     *
     * <p>The pair is the measurement. Both are points every row was read against and none is at;
     * they differ in whether anything was stopped from showing a row could be written there, which
     * is a difference between two things this compiler did and not between two models. So the
     * standing is the same, and what tells them apart is said where it is known — by the knowledge
     * itself, which says whether a budget ended the showing or nothing ever composed a value.
     */
    @Test
    void aShowingNothingEverMadeLeavesTheObligationUndecidedToo() {
        assertEquals(ObligationDisposition.Undecided.about(List.of(
                        new ObligationDisposition.Uncertainty
                                .WhetherARowCanBeWritten.NothingShowedIt())),
                ObligationDisposition.of(new ObligationCoverage.Missed(),
                        new WritabilityKnowledge.NoEvidence()),
                "a point nothing promises a row at is a point nobody could decide, not a point"
                        + " the model stopped owing — and what it is open on is that nothing"
                        + " showed it, which is not a budget having stopped anything");
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
     * <p>A reading that came to nothing and a showing that came to nothing are about different
     * things, and either one alone is a choice of which to tell.
     */
    @Test
    void twoOpenQuestionsAtOnePointAreBothSaid() {
        ObligationDisposition disposition = ObligationDisposition.of(
                new ObligationCoverage.Undecided(WeakeningSet.of(
                        new Weakening.BorderValueUnreadable(null,
                                ReadingGap.of(Incompleteness.Code.VALUE_TRUNCATED)))),
                prevented());

        assertEquals(ObligationDisposition.Undecided.about(List.of(
                        new ObligationDisposition.Uncertainty.WhetherARowIsThere.ReadingsStopped(
                                ReadingReasons.of(List.of(
                                        ReadingGap.of(Incompleteness.Code.VALUE_TRUNCATED)))),
                        new ObligationDisposition.Uncertainty.WhetherARowCanBeWritten.Stopped(
                                prevented()))),
                disposition,
                "the rows left one question open and the search left the other");
    }

    /**
     * A point nothing was read against is undecided about both questions, and stays owed.
     *
     * <p>Nothing was read is a fact about this build — it asked for no rows, or no row names the
     * behavior — and not about the model. Which of those it was is the coverage's own to say and is
     * carried there; what a verdict does with such an obligation is a policy of the build's, made
     * where the verdict selects what it is about, and not by the account quietly holding fewer
     * obligations than the model owes.
     */
    @Test
    void aPointNothingWasReadAgainstIsUndecidedAboutBoth() {
        assertEquals(ObligationDisposition.Undecided.about(List.of(
                        new ObligationDisposition.Uncertainty.WhetherARowIsThere.NothingWasRead(
                                ItemAssessment.Coverage.NotAsked.NO_ROWS),
                        new ObligationDisposition.Uncertainty
                                .WhetherARowCanBeWritten.NothingShowedIt())),
                ObligationDisposition.of(
                        new ObligationCoverage.NotMeasured(ItemAssessment.Coverage.NotAsked.NO_ROWS),
                        new WritabilityKnowledge.NoEvidence()),
                "nothing was read and nothing promises a row, both are open about it, and each"
                        + " says which of the two left it so");
    }

    /**
     * The law the table is for: no pair of answers leaves the account holding less.
     *
     * <p>Said over the states rather than over one pair. Every coverage crossed with every state of
     * the knowledge lands somewhere, and nowhere is an obligation dropped — a fold that grew a
     * fourth answer for a pair this compiler found hard would be answering a question about the
     * model with what it managed to do.
     */
    @Test
    void noPairOfAnswersTakesAnObligationOutOfTheAccount() {
        List<String> reached = new ArrayList<>();
        for (ObligationCoverage coverage : everyCoverage()) {
            for (WritabilityKnowledge knowledge : everyKnowledge()) {
                ObligationDisposition it = ObligationDisposition.of(coverage, knowledge);
                reached.add(it.getClass().getSimpleName());
                assertTrue(it instanceof ObligationDisposition.Met
                                || it instanceof ObligationDisposition.Unmet
                                || it instanceof ObligationDisposition.Undecided,
                        () -> coverage + " with " + knowledge + " is " + it
                                + ", which is not one of the three an owed point stands in");
            }
        }
        assertTrue(reached.contains("Met") && reached.contains("Unmet")
                        && reached.contains("Undecided"),
                "every state is reached by the table: " + reached);
    }

    /**
     * Weakening what is known may take a claim away and may not put one there.
     *
     * <p>The states are ordered by how much they claim: a row is there, no row is there, nobody can
     * say. A limit moves along that order downwards; moving across it — a miss becoming a hit — is
     * a resource policy answering a question about the model.
     */
    @Test
    void aLimitDoesNotTurnAMissIntoAHitOrBack() {
        for (ObligationCoverage coverage : everyCoverage()) {
            ObligationDisposition withGrounds = ObligationDisposition.of(coverage, established());
            for (WritabilityKnowledge weaker : List.of(prevented(),
                    new WritabilityKnowledge.NoEvidence())) {
                ObligationDisposition stopped = ObligationDisposition.of(coverage, weaker);
                assertTrue(weakensTo(withGrounds, stopped),
                        () -> "a limit moved " + coverage + " from " + withGrounds + " to " + stopped
                                + ", which is a verdict and not a loss of knowledge");
            }
        }
    }

    /**
     * Whether {@code after} claims no more than {@code before}.
     *
     * <p>A verdict may stand or become the one that claims nothing, and one that already claims
     * nothing may be open about more questions than before, since an open question is something
     * known about the point rather than a claim about the model.
     */
    private static boolean weakensTo(ObligationDisposition before, ObligationDisposition after) {
        return switch (before) {
            case ObligationDisposition.Met _, ObligationDisposition.Unmet _ ->
                    after.equals(before) || after instanceof ObligationDisposition.Undecided;
            case ObligationDisposition.Undecided it ->
                    after instanceof ObligationDisposition.Undecided then
                            && then.because().written().containsAll(it.because().written());
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

    private static List<WritabilityKnowledge> everyKnowledge() {
        return List.of(established(), prevented(), new WritabilityKnowledge.NoEvidence());
    }

    private static WritabilityKnowledge established() {
        return new WritabilityKnowledge.Established(ItemAssessment.WritabilityEvidence.of(
                Set.of(ItemAssessment.WritabilityEvidence.Ground.THE_RULES_PROVE_IT)));
    }

    private static WritabilityKnowledge.Prevented prevented() {
        return WritabilityKnowledge.Prevented.by(EstablishmentGap.Observation.of(
                EnumSet.of(Incompleteness.Code.VALUE_TRUNCATED)));
    }
}
