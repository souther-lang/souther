package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.EachWayItComesOut.Shown;
import souther.compiler.inputs.EachWayItComesOut.Stretch;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the arms of a choice show of each way a statement comes out, joined: a row takes one arm,
 * so a way is reached at a value where some arm reaches it there, never reached where every arm
 * never reaches it, and otherwise not shown. A value no arm holds is no value of the term.
 */
class AWayIsReachedWhereSomeArmReachesItTest {

    private static ExactCut from(long at) {
        return ExactCut.inclusive(ExactRatio.of(at));
    }

    private static ExactCut below(long at) {
        return ExactCut.exclusive(ExactRatio.of(at));
    }

    private static EachWayItComesOut everywhere(Shown holding, Shown failing) {
        return new EachWayItComesOut(Granularity.DENSE,
                List.of(new Stretch(null, null, holding, failing)));
    }

    private static Stretch only(EachWayItComesOut joined) {
        assertEquals(1, joined.stretches().size(), joined.toString());
        return joined.stretches().getFirst();
    }

    /** Every pair of what two arms show of one way, joined: reached beats the rest, and never
     *  needs both. */
    @Test
    void aWayIsReachedWhereEitherArmReachesItAndNeverWhereNeitherCan() {
        List<Shown> each = List.of(Shown.REACHED, Shown.NEVER, Shown.NOT_SHOWN);
        for (Shown one : each) {
            for (Shown other : each) {
                Shown expected = one == Shown.REACHED || other == Shown.REACHED ? Shown.REACHED
                        : one == Shown.NEVER && other == Shown.NEVER ? Shown.NEVER
                        : Shown.NOT_SHOWN;
                Stretch joined = only(EachWayItComesOut.eitherOf(List.of(
                        everywhere(one, Shown.NEVER), everywhere(other, Shown.NEVER))));
                assertEquals(expected, joined.holding(), one + " with " + other);
                assertEquals(Shown.NEVER, joined.failing(), one + " with " + other);
            }
        }
    }

    /**
     * The lesser of {@code x} and nought held at most {@code c}: the arm answering {@code x} holds
     * at every {@code c} and is not shown failing below nought; the arm answering nought fails
     * below nought and holds from nought up. Joined, the two ways are both reached below nought,
     * holding alone from nought up, and nought is the one place that changes.
     */
    @Test
    void aWayOneArmLeavesUnshownIsReachedByTheOther() {
        EachWayItComesOut answeringX = new EachWayItComesOut(Granularity.DENSE, List.of(
                new Stretch(null, below(0), Shown.REACHED, Shown.NOT_SHOWN),
                new Stretch(from(0), null, Shown.REACHED, Shown.NEVER)));
        EachWayItComesOut answeringNought = new EachWayItComesOut(Granularity.DENSE, List.of(
                new Stretch(null, below(0), Shown.NEVER, Shown.REACHED),
                new Stretch(from(0), null, Shown.REACHED, Shown.NEVER)));
        EachWayItComesOut joined =
                EachWayItComesOut.eitherOf(List.of(answeringX, answeringNought));
        assertEquals(List.of(new Stretch(null, below(0), Shown.REACHED, Shown.REACHED),
                new Stretch(from(0), null, Shown.REACHED, Shown.NEVER)), joined.stretches());
        assertTrue(joined.showsEveryValue());
        assertEquals(List.of(from(0)), joined.whereItTurns());
        assertFalse(answeringX.showsEveryValue());
    }

    /** A value no arm shows a way at is not shown that way, whatever the arms show beside it. */
    @Test
    void aValueNoArmShowsIsNotShown() {
        EachWayItComesOut one = new EachWayItComesOut(Granularity.DENSE, List.of(
                new Stretch(null, below(0), Shown.REACHED, Shown.NOT_SHOWN),
                new Stretch(from(0), null, Shown.REACHED, Shown.NEVER)));
        EachWayItComesOut joined = EachWayItComesOut.eitherOf(List.of(one, one));
        assertFalse(joined.showsEveryValue());
    }

    /**
     * An arm that holds no value somewhere reaches no way there, and a value no arm holds is none
     * of the term's: an arm over nought to five reached either way and one over three to nine
     * only failing, joined, are either way up to five, only failing past it to nine, and nothing
     * outside.
     */
    @Test
    void anArmReachesNothingWhereItHoldsNoValue() {
        EachWayItComesOut fromNought = new EachWayItComesOut(Granularity.DENSE,
                List.of(new Stretch(from(0), from(5), Shown.REACHED, Shown.REACHED)));
        EachWayItComesOut fromThree = new EachWayItComesOut(Granularity.DENSE,
                List.of(new Stretch(from(3), from(9), Shown.NEVER, Shown.REACHED)));
        EachWayItComesOut joined = EachWayItComesOut.eitherOf(List.of(fromNought, fromThree));
        assertEquals(List.of(
                new Stretch(from(0), from(5), Shown.REACHED, Shown.REACHED),
                new Stretch(below(5), from(9), Shown.NEVER, Shown.REACHED)),
                joined.stretches());
    }

    /** {@code x <= c}, as {@code x - c <= 0}, with {@code x} below nought or at nought or below,
     *  each way at the values of {@code c}. */
    private static EachWayItComesOut xAtMostC(NumericDomain.Bounds x) {
        List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                new WhatARelationLeavesUndivided.Term<>(List.of("c"), ExactRatio.of(-1),
                        NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, null, true,
                        Granularity.DENSE, NumericDomain.Bounds.OPEN),
                new WhatARelationLeavesUndivided.Term<>(List.of("x"), ExactRatio.ONE, x, x, null,
                        true, Granularity.DENSE, NumericDomain.Bounds.OPEN));
        WhatARelationLeavesUndivided.Leaves leaves = WhatARelationLeavesUndivided.leavesOf(terms,
                0, ExactRatio.ZERO, Rel.LE, String::equals, (one, other) -> true,
                Granularity.DENSE, null);
        return WhatARelationLeavesUndivided.eachWayItComesOut(leaves, terms, 0, ExactRatio.ZERO,
                Rel.LE, String::equals, (one, other) -> true, Granularity.DENSE, null,
                WhatARelationLeavesUndivided.Operations.NONE);
    }

    /**
     * A relation each way on its own where it is not shown both together: with {@code x} below
     * nought, {@code x <= c} holds at every {@code c} and fails at none from nought up, and below
     * nought is shown holding and not shown failing, there being no decimal {@code x} above the
     * finest step below nought. With {@code x} at nought or below it is shown either way below
     * nought, as the values it settles say.
     */
    @Test
    void aRelationShowsEachWayWhereItCannotShowBoth() {
        NumericDomain.Bounds belowNought =
                new NumericDomain.Bounds(null, Endpoint.exclusive(Count.of(0)));
        assertEquals(List.of(new Stretch(null, below(0), Shown.REACHED, Shown.NOT_SHOWN),
                new Stretch(from(0), null, Shown.REACHED, Shown.NEVER)),
                xAtMostC(belowNought).stretches());
        NumericDomain.Bounds atNoughtOrBelow =
                new NumericDomain.Bounds(null, Endpoint.inclusive(Count.of(0)));
        assertEquals(List.of(new Stretch(null, below(0), Shown.REACHED, Shown.REACHED),
                new Stretch(from(0), null, Shown.REACHED, Shown.NEVER)),
                xAtMostC(atNoughtOrBelow).stretches());
    }

    /** Whole numbers between two runs a step apart are none: the runs are beside each other, and
     *  where they show alike they are one. */
    @Test
    void twoRunsOfWholeNumbersAStepApartAreBesideEachOther() {
        EachWayItComesOut joined = EachWayItComesOut.eitherOf(List.of(
                new EachWayItComesOut(Granularity.DISCRETE, List.of(
                        new Stretch(null, from(0), Shown.REACHED, Shown.NEVER),
                        new Stretch(from(1), null, Shown.REACHED, Shown.NEVER)))));
        assertEquals(List.of(new Stretch(null, null, Shown.REACHED, Shown.NEVER)),
                joined.stretches());
        assertEquals(List.of(), joined.whereItTurns());
    }
}
