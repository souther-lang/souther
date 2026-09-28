package souther.compiler.partition;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.Numberings;
import souther.compiler.reading.PathAccess;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A behavior whose dependencies a way leaves open is searched once per way of standing them in, and
 * the answer about the model is what all of those runs found.
 *
 * <p>Each case says what it is over the runs, and the cases do not say the same thing. Whether an
 * obligation is answered by a row is a question every run has a share of the answer to, so the
 * order they were made in does not reach it. The reasons for finding none are all of them. And what
 * the reading of the body made of an arm is one value the runs share.
 *
 * <p>The rows themselves are not this question. Which of several a reader is offered is settled
 * where the rows are given the numbers they go out under, so a run that composed one is named here
 * and none of them is chosen.
 */
class WhatTheRunsCameToAtOneObligationIsWhatAllOfThemFoundTest {

    private static final Map<Integer, ArmProbe> PLACES = Numberings.arms(3);

    private static final ArmProbe ARM = PLACES.get(1);

    private static final ArmProbe ANOTHER_PLACE_OF_IT = PLACES.get(2);

    private static final CameToNothing NO_CANDIDATE =
            CameToNothing.metNothing(new Generator.UnresolvedCombination(List.of("days=low"),
                    Generator.UnresolvedCombination.Reason.NO_CANDIDATE_WAS_OFFERED));

    private static final CameToNothing THE_SEARCH_STOPPED =
            CameToNothing.metNothing(new Generator.UnresolvedCombination(List.of("days=high"),
                    Generator.UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED));

    private static final PathAccess NOTHING_ARRIVES = new PathAccess.Unreachable(
            PathAccess.Unreachable.Why.THE_CONDITION_NEVER_COMES_OUT_THAT_WAY);

    /**
     * Both runs' reasons, and the same answer whichever run was made first.
     *
     * <p>A budget one run stopped at and a rule another run's values were refused by are different
     * news, and the arm is answered by what was tried rather than by whichever run came first.
     */
    @Test
    void theReasonsOfEveryRunAnswerAnArmNoneOfThemComposedARowFor() {
        ArmDisposition.AcrossRuns oneWay = ArmDisposition.acrossRuns(List.of(
                new ArmDisposition.Unresolved(List.of(NO_CANDIDATE)),
                new ArmDisposition.Unresolved(List.of(THE_SEARCH_STOPPED))));
        ArmDisposition.AcrossRuns theOther = ArmDisposition.acrossRuns(List.of(
                new ArmDisposition.Unresolved(List.of(THE_SEARCH_STOPPED)),
                new ArmDisposition.Unresolved(List.of(NO_CANDIDATE))));

        assertEquals(oneWay, theOther, "the reasons of two runs, whichever run was made first");
    }

    /**
     * And what the runs met of this compiler's is every one of them, though the word is one.
     *
     * <p>How far a run got is the run's own: a way of standing the dependencies in reaches what it
     * reaches, and a figure one run ran into is a number somebody can raise whether or not the next
     * run got that far. So these add up, where the word they come back with has to agree — one is
     * an answer about the model and the other is how far this compiler went.
     */
    @Test
    void whatTheRunsMetOfThisCompilersIsEveryOneOfThem() {
        CameToNothing stoppedAtOne = new CameToNothing(NO_CANDIDATE.why(),
                CompositionShortfall.of(List.of(CompositionBudget.NUMBERS_OF_A_SET_TRIED)));
        CameToNothing stoppedAtAnother = new CameToNothing(NO_CANDIDATE.why(),
                CompositionShortfall.of(List.of(CompositionBudget.STEPS_A_SEARCH_MAY_TAKE)));

        ClassDisposition.AcrossRuns both = ClassDisposition.acrossRuns(List.of(
                new ClassDisposition.Unresolved(stoppedAtOne),
                new ClassDisposition.Unresolved(stoppedAtAnother)));

        assertEquals(new ClassDisposition.AcrossRuns.Unresolved(new CameToNothing(
                        NO_CANDIDATE.why(),
                        CompositionShortfall.of(List.of(CompositionBudget.NUMBERS_OF_A_SET_TRIED,
                                CompositionBudget.STEPS_A_SEARCH_MAY_TAKE)))),
                both,
                "both figures, so a reader is told everything raising would reach");
    }

    /** And the same answer for one run asked about twice, which is the one run's answer. */
    @Test
    void oneRunCountedTwiceAnswersWhatItAnsweredOnce() {
        ArmDisposition.Unresolved run = new ArmDisposition.Unresolved(List.of(NO_CANDIDATE));

        assertEquals(ArmDisposition.acrossRuns(List.of(run)),
                ArmDisposition.acrossRuns(List.of(run, run)),
                "one run's reasons, however many times the run is counted");
    }

    /**
     * A row of any run answers the arm, and every run that composed one is named.
     *
     * <p>Which run is named first is the order they were made in, so what is the same either way
     * round is the rows and the places they went through — not the positions they are held under.
     */
    @Test
    void aRowOfAnyRunAnswersTheArmWhicheverRunWasMadeFirst() {
        ArmDisposition.Built here = new ArmDisposition.Built(new RowId(0), ARM);
        ArmDisposition.Built there =
                new ArmDisposition.Built(new RowId(1), ANOTHER_PLACE_OF_IT);

        ArmDisposition.AcrossRuns.Built oneWay = assertInstanceOf(
                ArmDisposition.AcrossRuns.Built.class,
                ArmDisposition.acrossRuns(List.of(here, there)));
        ArmDisposition.AcrossRuns.Built theOther = assertInstanceOf(
                ArmDisposition.AcrossRuns.Built.class,
                ArmDisposition.acrossRuns(List.of(there, here)));

        assertEquals(whatWasBuilt(oneWay), whatWasBuilt(theOther),
                "the rows of two runs and the places they went through, either way round");
        assertEquals(Map.of(here, 1L, there, 1L), whatWasBuilt(oneWay));
    }

    /**
     * A row of one run answers an arm another run had nowhere to look for.
     *
     * <p>A run reaches an arm by composing a row steered there or by watching a row composed for
     * something else go through it. What a row's run goes through is what the dependencies it was
     * given answer, so an arm no way into can be named is an arm a row may still be seen taking —
     * and it is answered by that row, not by the reading that had nothing to try.
     */
    @Test
    void aRowOfOneRunAnswersAnArmAnotherHadNowhereToLookFor() {
        ArmDisposition.Built reached = new ArmDisposition.Built(new RowId(0), ARM);

        ArmDisposition.AcrossRuns.Built built = assertInstanceOf(
                ArmDisposition.AcrossRuns.Built.class,
                ArmDisposition.acrossRuns(List.of(
                        new ArmDisposition.NoWayIn(NOTHING_ARRIVES), reached)));

        assertEquals(List.of(reached), built.witnesses().stream()
                .map(ArmDisposition.AcrossRuns.Witness::built).toList());
    }

    /** What the reading made of an arm every run had nowhere to look for, which they all share. */
    @Test
    void anArmNoRunHadAnywhereToLookForIsAnsweredByWhatTheReadingSays() {
        ArmDisposition.NoWayIn read = new ArmDisposition.NoWayIn(NOTHING_ARRIVES);

        assertEquals(new ArmDisposition.AcrossRuns.NoWayIn(List.of(NOTHING_ARRIVES)),
                ArmDisposition.acrossRuns(List.of(read, read)));
    }

    /** A class is answered by a row of any run, the same way an arm is. */
    @Test
    void aRowOfAnyRunAnswersTheClassWhicheverRunWasMadeFirst() {
        ClassDisposition.Built here = new ClassDisposition.Built(new RowId(0));
        ClassDisposition.Unresolved nothing = new ClassDisposition.Unresolved(NO_CANDIDATE);

        assertInstanceOf(ClassDisposition.AcrossRuns.Built.class,
                ClassDisposition.acrossRuns(List.of(here, nothing)));
        assertInstanceOf(ClassDisposition.AcrossRuns.Built.class,
                ClassDisposition.acrossRuns(List.of(nothing, here)));
    }

    /**
     * And the reason where none of them did, which is the one reason they all give.
     *
     * <p>One and not all of them, because what a run stands the dependencies in with reaches a
     * composed row and decides nothing about whether a value builds or what a refusal says.
     */
    @Test
    void aClassNoRunComposedARowForIsAnsweredByTheReasonTheyAllGive() {
        ClassDisposition.Unresolved nothing = new ClassDisposition.Unresolved(NO_CANDIDATE);

        assertEquals(new ClassDisposition.AcrossRuns.Unresolved(NO_CANDIDATE),
                ClassDisposition.acrossRuns(List.of(nothing, nothing)));
    }

    /**
     * What the runs composed, counted rather than ordered.
     *
     * <p>Which run a row came from is the order the runs were made in, so a witness compares by
     * what the run answered with. Counted and not gathered into a set, so that a fold dropping one
     * of two runs that answered alike is a difference here.
     */
    private static Map<ArmDisposition.Built, Long> whatWasBuilt(
            ArmDisposition.AcrossRuns.Built built) {
        return built.witnesses().stream()
                .collect(Collectors.groupingBy(ArmDisposition.AcrossRuns.Witness::built,
                        Collectors.counting()));
    }
}
