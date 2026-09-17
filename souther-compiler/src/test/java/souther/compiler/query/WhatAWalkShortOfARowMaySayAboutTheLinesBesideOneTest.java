package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.Demand;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.OrderedAffineBoundary;
import souther.compiler.partition.QuantityKey;
import souther.compiler.partition.ReadingGap;
import souther.compiler.partition.StandingAtAPoint;
import souther.compiler.partition.WayToTheBorder;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a walk that went without a row may conclude about the lines beside a border.
 *
 * <p>The asymmetry, and the one place it is decided. A row read is a constraint on which lines the
 * rows allow, so reading more of them leaves fewer standing and never more: a walk short of a row
 * may say that nothing else stands, because what it read was enough, and may not name a line that
 * does, because the row it went without is exactly what would have ruled that line out.
 *
 * <p><b>The pairs below are one border and one set of rows, with only the walk's own answer about
 * itself moved.</b> Nothing about the model differs between them, so a verdict that turns on it is a
 * verdict about this compiler's walk — and that is what a walk saying whether it read everything is
 * for.
 *
 * <p>Held at the answer rather than through a report, because what a report shows of a partial walk
 * is a model whose rows are hard to write and whose reading is harder to stop at the right place.
 * What is asked here is the rule, put to the rows it is a rule about.
 */
class WhatAWalkShortOfARowMaySayAboutTheLinesBesideOneTest {

    /** The rows have met every point of the border, which is what makes this question due. What
     *  happens before that is its own case below. */
    private static final boolean MET = true;

    /** Rows that leave `-3 * x + y = 0` standing beside `-2 * x + y = 0`: every one of them answers
     *  the same under both. */
    private static final int[][] ALIKE_UNDER_BOTH = {{0, 0}, {0, 1}, {13, 23}, {12, 24}};

    /** The same rows with one added that the two answer differently at, which rules it out. */
    private static final int[][] AND_ONE_THAT_TELLS_THEM_APART =
            {{0, 0}, {0, 1}, {13, 23}, {12, 24}, {1, 3}};

    @Test
    void aWalkThatReadEveryRowNamesTheLineTheyLeaveStanding() {
        AnotherLineTheRowsAllow said = of(ALIKE_UNDER_BOTH, everyOne());

        AnotherLineTheRowsAllow.OneDoes named =
                assertInstanceOf(AnotherLineTheRowsAllow.OneDoes.class, said,
                        () -> "these rows answer alike under both lines: " + said);
        assertEquals("-3 * x + y = 0", named.label(),
                "and the line they leave standing is the one weighing `x` one more");
    }

    @Test
    void aWalkShortOfARowMayNotNameIt() {
        AnotherLineTheRowsAllow said = of(ALIKE_UNDER_BOTH, stoppedShort());

        AnotherLineTheRowsAllow.CouldNotTell open =
                assertInstanceOf(AnotherLineTheRowsAllow.CouldNotTell.class, said,
                        () -> "the row it went without is what would have ruled that line out: "
                                + said);
        assertInstanceOf(AnotherLineTheRowsAllow.Unsettled.RowsIncomplete.class, open.why(),
                "and what stopped it is what the walk says of itself");
    }

    @Test
    void andMaySayThatNothingStandsFromTheRowsItDidRead() {
        assertEquals(AnotherLineTheRowsAllow.NONE_DOES,
                of(AND_ONE_THAT_TELLS_THEM_APART, stoppedShort()),
                "a line none of the rows it read allows is one none of the rest would allow"
                        + " either, so a short walk settles this way and not the other");
    }

    /** Which is not the walk answering alike whatever it read: the same short walk over the rows
     *  above comes to the other answer. */
    @Test
    void soTheTwoAnswersOfAShortWalkAreTheRowsAndNotTheWalk() {
        assertTrue(of(ALIKE_UNDER_BOTH, stoppedShort())
                        instanceof AnotherLineTheRowsAllow.CouldNotTell
                && of(AND_ONE_THAT_TELLS_THEM_APART, stoppedShort())
                        instanceof AnotherLineTheRowsAllow.NoneDoes,
                "one short walk settles it and one does not, over the same border");
    }

    /**
     * A shortfall that is not a reading: the rows were read in full and a walk that went without
     * nothing still could not put the question.
     *
     * <p>Said as a question that could not be settled rather than as one that does not arise. A rule
     * that names a value divides the quantity at the value it names, so there is a line one step
     * from it and weighing a position differently is as much a fault there — what is missing is a
     * side to keep a row on, which is a thing to write.
     */
    @Test
    void aRuleThatNamesAValueIsAQuestionNobodyHereCanPut() {
        Border names = TheLinesBesideABorder.aBorderThatNamesAValue();

        AnotherLineTheRowsAllow said = AnotherLineTheRowsAllow.of(names, MET,
                () -> new StandingAtAPoint.RowsRead(rowsOf(names, ALIKE_UNDER_BOTH),
                        Set.of(), StandingAtAPoint.ReadingsTried.EVERY_ONE, false),
                List.of(), WayToTheBorder.UNTOUCHED);

        AnotherLineTheRowsAllow.CouldNotTell open =
                assertInstanceOf(AnotherLineTheRowsAllow.CouldNotTell.class, said,
                        () -> "there is a line one step from it: " + said);
        assertInstanceOf(AnotherLineTheRowsAllow.Unsettled.NoStrategyForIt.class, open.why(),
                "and what is missing is a strategy rather than the question");
    }

    /** A line on one position, which has no line one step from it however the rows fall. */
    @Test
    void andABoundOnOnePositionIsAQuestionThatDoesNotArise() {
        AnotherLineTheRowsAllow said = AnotherLineTheRowsAllow.of(
                TheLinesBesideABorder.aBoundOnOnePosition(), MET,
                () -> {
                    throw new AssertionError("the rows are not read for a line with no neighbour");
                },
                List.of(), WayToTheBorder.UNTOUCHED);

        assertEquals(new AnotherLineTheRowsAllow.NoSuchQuestion(
                        AnotherLineTheRowsAllow.Reason.THE_LINE_IS_ON_ONE_POSITION), said,
                "weighed one less it is nothing and weighed one more it is the same line");
    }

    /** What the walk says of itself where it read everything. */
    private static StandingAtAPoint.ReadingsTried everyOne() {
        return StandingAtAPoint.ReadingsTried.EVERY_ONE;
    }

    /** And where it stopped at the figure one point is tried against. */
    private static StandingAtAPoint.ReadingsTried stoppedShort() {
        return new StandingAtAPoint.ReadingsTried.StoppedAtTheLimit(4);
    }

    /**
     * The line it names answers what the model's answers at every row read, and answers differently
     * at the input it names.
     *
     * <p>Which is what makes it the line the rows allow, and what a row settles it by. The
     * threshold was chosen to keep every row the model keeps and refuse every row it refuses, so
     * the two part company nowhere the rows already stand — put to the values here rather than
     * taken from how the threshold was worked out, because that is how a row offered later is
     * weighed ({@link AnotherLineTheRowsAllow.OneDoes#keeps}).
     */
    @Test
    void theLineItNamesAnswersAlikeAtEveryRowAndDiffersAtTheInputItNames() {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();
        OrderedAffineBoundary drawn = OrderedAffineBoundary.of(border);
        AnotherLineTheRowsAllow.OneDoes named = assertInstanceOf(
                AnotherLineTheRowsAllow.OneDoes.class, of(ALIKE_UNDER_BOTH, everyOne()));

        for (Map<NumericTerm, Place> row : rowsOf(border, ALIKE_UNDER_BOTH)) {
            assertEquals(drawn.satisfiedBy(row), named.keeps(row),
                    () -> "the two lines answer alike at every row that was read: " + row);
        }
        Map<NumericTerm, Place> apart = rowsOf(border, new int[][] {{1, 3}}).getFirst();
        assertNotEquals(drawn.satisfiedBy(apart), named.keeps(apart),
                () -> "and differently at the input the answer names: " + apart);
    }

    /**
     * The answer for those rows, with the walk saying it read everything or that it did not.
     *
     * <p>The rows are the same either way. What moves is one field of the walk's own answer about
     * itself, which is what makes the pair a pair.
     */
    private static AnotherLineTheRowsAllow of(int[][] rows,
                                              StandingAtAPoint.ReadingsTried tried) {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();
        return AnotherLineTheRowsAllow.of(border, MET,
                () -> new StandingAtAPoint.RowsRead(rowsOf(border, rows), Set.of(), tried, false),
                List.of(), WayToTheBorder.UNTOUCHED);
    }

    /** One reading per row, each value on the term the quantity reads it at. */
    private static List<Map<NumericTerm, Place>> rowsOf(Border border, int[][] rows) {
        List<NumericTerm> terms = new ArrayList<>(
                QuantityKey.of(border.cut().of().direction()).direction().keySet());
        terms.sort(Comparator.comparing(NumericTerm::toString));
        List<Map<NumericTerm, Place>> out = new ArrayList<>();
        for (int[] row : rows) {
            Map<NumericTerm, Place> at = new LinkedHashMap<>();
            for (int i = 0; i < terms.size(); i++) {
                at.put(terms.get(i), Count.of(row[i]));
            }
            out.add(at);
        }
        return out;
    }

    /**
     * An answer that could not be settled weakens the measure the lines are read by, and a settled
     * one does not.
     *
     * <p>Which is what carries the whole of this to a verdict. A reading of the lines answers two
     * questions, so a reading short of either is short — and a reader that had only the first would
     * call a model settled over a question nobody could put.
     */
    @Test
    void anUnsettledAnswerIsWhatTheReadingOfTheLinesWentWithout() {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();

        assertTrue(assessed(border, AnotherLineTheRowsAllow.NONE_DOES)
                        .besideWeakening().isEmpty(),
                "a line no other line survives beside is settled, and weakens nothing");
        assertTrue(assessed(border, new AnotherLineTheRowsAllow.NoSuchQuestion(
                        AnotherLineTheRowsAllow.Reason.THE_LINE_IS_ON_ONE_POSITION))
                        .besideWeakening().isEmpty(),
                "and so is one there was never a question about");
        assertTrue(assessed(border, new AnotherLineTheRowsAllow.CouldNotTell(
                        new AnotherLineTheRowsAllow.Unsettled.RowsIncomplete(
                                ReadingReasons.of(Set.of(ReadingGap.NO_VALUE),
                                        StandingAtAPoint.ReadingsTried.EVERY_ONE))))
                        .besideWeakening().causes().stream()
                        .anyMatch(each -> each instanceof Weakening.BorderValueUnreadable),
                "a walk that went without a row says so in the words a reading answers in");
        assertTrue(assessed(border, new AnotherLineTheRowsAllow.CouldNotTell(
                        new AnotherLineTheRowsAllow.Unsettled.NoStrategyForIt(
                                AnotherLineTheRowsAllow.Strategy.A_RULE_THAT_NAMES_A_VALUE)))
                        .besideWeakening().causes().stream()
                        .anyMatch(each -> each
                                instanceof Weakening.ABorderNotHeldAgainstTheLinesBesideIt),
                "and a strategy nobody wrote says so in words of its own, since a reader acts on"
                        + " the two differently");
    }

    /** The border with nothing established at any of its points, which is not what these are
     *  about: what moves between them is the answer beside the points. */
    private static BorderAssessment assessed(Border border, AnotherLineTheRowsAllow beside) {
        Map<DomainPoint, ItemAssessment> items = new LinkedHashMap<>();
        border.answers().keySet().forEach(point -> items.put(point,
                border.demand(point) instanceof Demand.NotOwed not
                        ? new ItemAssessment.NotOwed(not.reason())
                        : new ItemAssessment.Owed(border.demand(point).criterion(),
                                new Measurement.NotMeasured<>(
                                        ItemAssessment.Coverage.NotAsked.NO_ROWS),
                                ItemAssessment.WritabilityProjection.NOT_COMPUTED,
                                SearchOutcomes.none())));
        return new BorderAssessment(border, items, beside);
    }

    /**
     * A line the two part company with only where no row arrives is not a line anybody can be shown.
     *
     * <p>The rows are the ones that leave {@code -3 * x + y = 0} standing, so what moves between
     * this and the first case is the way to the border and nothing else. Here the way holds
     * {@code x} at nought, and every input the two lines answer differently at has {@code x}
     * somewhere else — so the two are one line as far as a row of this behavior goes, and there is
     * no fault to name.
     */
    @Test
    void aLineThatPartsCompanyWhereNoRowArrivesIsNotNamed() {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();

        AnotherLineTheRowsAllow said = AnotherLineTheRowsAllow.of(border, MET,
                () -> new StandingAtAPoint.RowsRead(rowsOf(border, ALIKE_UNDER_BOTH),
                        Set.of(), StandingAtAPoint.ReadingsTried.EVERY_ONE, false),
                List.of(), TheLinesBesideABorder.aWayThatHoldsXAtNought());

        AnotherLineTheRowsAllow.CouldNotTell open =
                assertInstanceOf(AnotherLineTheRowsAllow.CouldNotTell.class, said,
                        () -> "the rows leave a line standing and no row reaches where it differs: "
                                + said);
        assertInstanceOf(AnotherLineTheRowsAllow.Unsettled.NoReachableDistinguisher.class,
                open.why(), "which is what is missing, and not a row");
    }

    /**
     * A condition over a position the border is not on does not turn every input away.
     *
     * <p>What a row is read at is the quantity its line is on, so an input stepped along that line
     * holds no number at any other position — and a condition on the way over one of those cannot be
     * read there. Read as unknown and unknown as unreachable, a border with any earlier rule
     * mentioning a position beside it would name no input at all, and a model whose rows do leave a
     * line standing would come back open on this compiler rather than on the rows.
     *
     * <p>It is decided without that number: the row passed the condition, and what the step does to
     * it is a number the step alone gives, because the positions it does not move are the same at
     * both ends.
     */
    @Test
    void aConditionOverAPositionTheBorderIsNotOnIsStillDecided() {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();

        AnotherLineTheRowsAllow said = AnotherLineTheRowsAllow.of(border, MET,
                () -> new StandingAtAPoint.RowsRead(rowsOf(border, ALIKE_UNDER_BOTH),
                        Set.of(), StandingAtAPoint.ReadingsTried.EVERY_ONE, false),
                List.of(), TheLinesBesideABorder.aWayOverAPositionTheBorderIsNotOn());

        AnotherLineTheRowsAllow.OneDoes named =
                assertInstanceOf(AnotherLineTheRowsAllow.OneDoes.class, said,
                        () -> "the rows leave this line standing and an input still reaches: "
                                + said);
        assertNotNull(named.tellsApartAt(), "and the input is named");
    }

    /**
     * And a condition on the way that nothing here took in turns every input away.
     *
     * <p>What such a way leaves is not known to be what reaches the border, so an input past it is
     * one nothing here can say a row arrives at. Read as arriving, a line two borders part company
     * at somewhere unreachable would go out as a fault and the row asked for would show nothing.
     */
    @Test
    void andAConditionNothingTookInLeavesNothingToNameEither() {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();

        AnotherLineTheRowsAllow said = AnotherLineTheRowsAllow.of(border, MET,
                () -> new StandingAtAPoint.RowsRead(rowsOf(border, ALIKE_UNDER_BOTH),
                        Set.of(), StandingAtAPoint.ReadingsTried.EVERY_ONE, false),
                List.of(), TheLinesBesideABorder.aWayWithAConditionNobodyRead());

        assertInstanceOf(AnotherLineTheRowsAllow.Unsettled.NoReachableDistinguisher.class,
                assertInstanceOf(AnotherLineTheRowsAllow.CouldNotTell.class, said).why(),
                "nothing here can say a row arrives past a condition nobody took in");
    }

    /**
     * And before the rows have met the border's points, the question is not due and the rows are
     * not read for it.
     *
     * <p>Which is the whole of what keeps one border from being two sentences. A border short of a
     * row at one of its points is short of the rows that show where it falls, and a row written for
     * that may well answer this one too.
     */
    @Test
    void andTheQuestionIsNotDueBeforeTheRowsHaveMetThePoints() {
        AnotherLineTheRowsAllow said = AnotherLineTheRowsAllow.of(
                TheLinesBesideABorder.aLineOverTwoPositions(), false,
                () -> {
                    throw new AssertionError("the rows are not read before the question is due");
                },
                List.of(), WayToTheBorder.UNTOUCHED);

        assertEquals(AnotherLineTheRowsAllow.NOT_DUE_YET, said,
                "what the rows are short of here is what the points say they are short of");
    }

    /** Held apart from the cases above so the reasons a walk gives are the subject there. */
    @Test
    void aWalkThatMetAReadingGapIsAsShortAsOneThatStopped() {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();
        AnotherLineTheRowsAllow said = AnotherLineTheRowsAllow.of(border, MET,
                () -> new StandingAtAPoint.RowsRead(rowsOf(border, ALIKE_UNDER_BOTH),
                        Set.of(ReadingGap.NO_VALUE), StandingAtAPoint.ReadingsTried.EVERY_ONE,
                        false),
                List.of(), WayToTheBorder.UNTOUCHED);

        assertNotNull(said);
        assertInstanceOf(AnotherLineTheRowsAllow.CouldNotTell.class, said,
                "a row that could not be read is a row that was gone without, whatever the walk"
                        + " managed over the rest");
    }
}
