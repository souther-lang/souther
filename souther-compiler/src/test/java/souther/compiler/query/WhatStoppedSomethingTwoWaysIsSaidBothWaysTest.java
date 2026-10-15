package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.AnswerChange;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.ReplacementDisposition;
import souther.compiler.partition.StandingAtAPoint;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.StoppedReading;
import souther.compiler.values.UnreadReason;
import souther.compiler.values.ValueSet;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Where two meetings of one thing went two ways, what they come to holds both.
 *
 * <p>Each place that puts meetings together used to keep one of them: the host's stop over a
 * figure, a figure over the host's stop, the last row's limit over the first's, the first rule's
 * figure over the second's. What was dropped was true, and a reader was told either that no figure
 * was reached or that nothing else stood in the way.
 */
class WhatStoppedSomethingTwoWaysIsSaidBothWaysTest {

    private static final Figure STEPS = WorkFigure.EVALUATION_STEPS.at(100);

    private static final Figure DEPTH = WorkFigure.OBSERVED_DEPTH.at(3);

    /**
     * One reason a rewrite was left open, met at a figure by one run and at the host's stack by
     * another, is one way holding both: the figure is named, and a wider run may decide the rewrite
     * because the run held by the figure alone may come back telling.
     */
    @Test
    void aWayMetAtAFigureByOneRunAndAtNoAllowanceByAnotherHoldsBoth() {
        ReplacementEvidence.Undecided.LeftOpen open = ReplacementEvidence.Undecided.LeftOpen.of(
                List.of(ReplacementEvidence.Undecided.Way.atFigures(
                                ReplacementEvidence.Undecided.Why.A_RUN_DID_NOT_COME_BACK,
                                List.of(STEPS)),
                        ReplacementEvidence.Undecided.Way.atNoAllowance(
                                ReplacementEvidence.Undecided.Why.A_RUN_DID_NOT_COME_BACK)));

        assertEquals(1, open.ways().size(), open::toString);
        ReplacementEvidence.Undecided.Way way = open.ways().getFirst();
        assertEquals(List.of(STEPS), way.figures());
        assertEquals(true, way.met().atNoFigure(), "and the host's stop is not dropped");
        assertEquals(RunSensitivity.MAY_CHANGE, way.runSensitivity());
    }

    /**
     * And one run held at a figure and at something no figure decides at once is not one a wider
     * run tells: past the figure, the other stop is still there.
     */
    @Test
    void aRunHeldAtAFigureAndAtSomethingElseAtOnceIsNoneAWiderRunTells() {
        ReplacementEvidence.Undecided.Way way = new ReplacementEvidence.Undecided.Way(
                ReplacementEvidence.Undecided.Why.A_RUN_DID_NOT_COME_BACK,
                ReplacementDisposition.Met.once(List.of(STEPS), true));

        assertEquals(List.of(STEPS), way.figures(), "the figure was reached, and is named");
        assertEquals(RunSensitivity.UNAFFECTED, way.runSensitivity());
    }

    /** Two searches for one rewrite that ended one way, each met differently, met it both ways. */
    @Test
    void twoSearchesThatEndedOneWayDifferentlyEndedItBothWays() {
        ReplacementDisposition both = ReplacementDisposition.together(
                new ReplacementDisposition.NoneFound(Map.of(
                        ReplacementDisposition.Ended.A_RUN_DID_NOT_COME_BACK,
                        ReplacementDisposition.Met.at(List.of(STEPS)))),
                new ReplacementDisposition.NoneFound(
                        ReplacementDisposition.Ended.A_RUN_DID_NOT_COME_BACK));

        assertEquals(new ReplacementDisposition.NoneFound(Map.of(
                        ReplacementDisposition.Ended.A_RUN_DID_NOT_COME_BACK,
                        new ReplacementDisposition.Met(List.of(STEPS), true, true))),
                both);
        assertEquals(List.of(new ReplacementEvidence.Undecided.Way(
                        ReplacementEvidence.Undecided.Why.A_RUN_DID_NOT_COME_BACK,
                        new ReplacementDisposition.Met(List.of(STEPS), true, true))),
                Replacements.Measured.whyNoneFound(
                        ((ReplacementDisposition.NoneFound) both).ended()));
    }

    /**
     * What kept two answers from being told apart is asked of both: a body that ran out at one
     * figure and a rewrite at another were held by both, and a body that answered nothing beside a
     * rewrite that ran out is held by the body whatever the rewrite reached.
     */
    @Test
    void whatKeptTwoAnswersUntoldIsAskedOfBoth() {
        assertEquals(new AnswerChange.Untold(List.of(DEPTH, STEPS), false),
                AnswerChange.untold(new AnswerObservation.RanOut(Optional.of(STEPS)),
                        new AnswerObservation.RanOut(Optional.of(DEPTH))));
        assertEquals(new AnswerChange.Untold(List.of(DEPTH, STEPS), false),
                AnswerChange.untold(
                        new AnswerObservation.Answered(new ObservedValue.Sequence(
                                List.of(new ObservedValue.Truncated(DEPTH)))),
                        new AnswerObservation.RanOut(Optional.of(STEPS))));
        assertEquals(new AnswerChange.Untold(List.of(STEPS), true),
                AnswerChange.untold(new AnswerObservation.NotAnswered(),
                        new AnswerObservation.RanOut(Optional.of(STEPS))));
        assertNull(AnswerChange.untold(
                        new AnswerObservation.Answered(new ObservedValue.Integer(1)),
                        new AnswerObservation.NotAnswered()),
                "an answer against nothing is one that changed");
    }

    /** Two rows of one point stopped at two limits leave the point stopped at both. */
    @Test
    void twoRowsStoppedAtTwoLimitsLeaveThePointStoppedAtBoth() {
        Figure few = WorkFigure.READINGS_OF_A_ROW_AT_A_POINT.at(64);
        Figure many = WorkFigure.READINGS_OF_A_ROW_AT_A_POINT.at(128);

        assertEquals(new StandingAtAPoint.ReadingsTried.StoppedAtTheLimit(List.of(few, many)),
                StandingAtAPoint.ReadingsTried.EVERY_ONE
                        .and(new StandingAtAPoint.ReadingsTried.StoppedAtTheLimit(many))
                        .and(StandingAtAPoint.ReadingsTried.EVERY_ONE)
                        .and(new StandingAtAPoint.ReadingsTried.StoppedAtTheLimit(few)));
    }

    /** Two rules of one position unread for one reason at two figures leave it unread at both. */
    @Test
    void twoRulesUnreadForOneReasonAtTwoFiguresLeaveThePositionUnreadAtBoth() {
        Figure oneMachine = WorkFigure.ADMITTED_VALUES_ONE_MACHINE.at("10 states or 20 looked at");
        Figure inAll = WorkFigure.ADMITTED_VALUES_IN_ALL.at("30 states built and 20 looked at");
        Set<AdmissibleSet.Widening> why = new LinkedHashSet<>();
        why.add(new AdmissibleSet.Widening.RuleUnread(
                new StoppedReading(UnreadReason.PATTERN_TOO_COSTLY, oneMachine)));
        why.add(new AdmissibleSet.Widening.RuleUnread(
                new StoppedReading(UnreadReason.PATTERN_TOO_COSTLY, inAll)));

        assertEquals(new StoppedReading(UnreadReason.PATTERN_TOO_COSTLY,
                        List.of(oneMachine, inAll)),
                AdmissibleSet.wider(ValueSet.ANY, why).whyPartial());
    }
}
