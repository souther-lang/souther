package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What ways that meet at a relation leave a whole-number term, read once they have met: at each
 * value, a way the relation comes out is reached where some way reaches it and never where none
 * can ({@link EachWayItComesOut#eitherOf}), and what the ways leave is read once they have met
 * ({@link EachWayItComesOut#leaves}).
 *
 * <p>Along a way whose own statements decide the relation, a value is reached the way it comes
 * out only where the term is shown to take it and the rows there are computed
 * ({@link WhatARelationLeavesUndivided#alongAWayThatDecidesIt}): that every row comes out one way
 * says how a row would come out, and not that there is one.
 */
class WaysMeetingAtARelationAreReadOnceTheyHaveMetTest {

    private static NumericDomain.Bounds run(Long least, Long greatest) {
        return new NumericDomain.Bounds(
                least == null ? null : Endpoint.inclusive(Count.of(least)),
                greatest == null ? null : Endpoint.inclusive(Count.of(greatest)));
    }

    /**
     * A way along which every row has the relation come out {@code holds}, the term lying in
     * {@code holds} and shown to take {@code realizes}, the relation being the term against
     * nought and the type stopping at {@code greatest}.
     */
    private static EachWayItComesOut decided(NumericDomain.Bounds lies,
                                             NumericDomain.Bounds realizes, boolean holds,
                                             BigInteger greatest) {
        WhatARelationLeavesUndivided.Term<String> it = new WhatARelationLeavesUndivided.Term<>(
                List.of("x"), ExactRatio.ONE, lies, realizes, null, true, Granularity.DISCRETE,
                null);
        return WhatARelationLeavesUndivided.alongAWayThatDecidesIt(List.of(it), 0,
                ExactRatio.ZERO, holds, Granularity.DISCRETE, greatest,
                WhatARelationLeavesUndivided.Operations.NONE);
    }

    /** The same, every value the term lies at shown taken, and no size stopping a row. */
    private static EachWayItComesOut decided(NumericDomain.Bounds lies, boolean holds) {
        return decided(lies, lies, holds, null);
    }

    private static EachWayItComesOut met(EachWayItComesOut... ways) {
        return EachWayItComesOut.eitherOf(List.of(ways));
    }

    private static WhatARelationLeavesUndivided.Leaves left(EachWayItComesOut ways) {
        return ways.leaves(Set.of(), Set.of());
    }

    private static WhatARelationLeavesUndivided.Leaves settled(Long from, Long to, boolean holds,
                                                               Long least, Long greatest) {
        return WhatARelationLeavesUndivided.Leaves.Settled.ofWhole(
                List.of(WhatARelationLeavesUndivided.SettledRun.whole(
                        from == null ? null : BigInteger.valueOf(from),
                        to == null ? null : BigInteger.valueOf(to), holds)),
                least == null ? null : BigInteger.valueOf(least),
                greatest == null ? null : BigInteger.valueOf(greatest));
    }

    private static final WhatARelationLeavesUndivided.Leaves UNDIVIDED =
            new WhatARelationLeavesUndivided.Leaves.Undivided();

    /** The other way is never reached, and this one only at the values the term is shown to
     *  take. */
    @Test
    void aWayThatDecidesTheRelationReachesItsWayOnlyWhereTheTermIsShownTaken() {
        EachWayItComesOut way = decided(run(0L, null), run(5L, 9L), true, null);

        List<EachWayItComesOut.Shown> reached = List.of(EachWayItComesOut.Shown.REACHED,
                EachWayItComesOut.Shown.NEVER);
        List<EachWayItComesOut.Shown> notShown = List.of(EachWayItComesOut.Shown.NOT_SHOWN,
                EachWayItComesOut.Shown.NEVER);
        assertEquals(List.of(notShown, notShown, reached, reached, notShown, notShown),
                List.of(shownAt(way, 0), shownAt(way, 4), shownAt(way, 5), shownAt(way, 9),
                        shownAt(way, 10), shownAt(way, 1000)));
        assertNull(shownAt(way, -1), "no row is at a value the term does not lie at");
    }

    /** A term held to a run and shown to take none of it has no row shown there: two ways
     *  deciding the relation two ways do not show a value either way. */
    @Test
    void aTermHeldToARunButShownToTakeNoneOfItShowsNoRow() {
        EachWayItComesOut holding = decided(run(0L, 9L), null, true, null);
        EachWayItComesOut failing = decided(run(0L, 9L), false);

        assertNull(left(met(holding, failing)));
    }

    /** A row whose sum may pass where the type stops is no row shown, wherever the term is
     *  shown to take a value. */
    @Test
    void aValueWhoseRowsMayStopIsNotShownReached() {
        EachWayItComesOut holding = decided(run(0L, 1000L), run(0L, 1000L), true,
                BigInteger.valueOf(100));
        EachWayItComesOut failing = decided(run(0L, 1000L), false);

        assertNull(left(met(holding, failing)));
        assertEquals(UNDIVIDED, left(met(decided(run(0L, 1000L), run(0L, 1000L), true,
                BigInteger.valueOf(1000)), failing)));
    }

    @Test
    void twoWaysThatComeOutTwoWaysAtTheSameValuesLeaveThemEitherWay() {
        assertEquals(UNDIVIDED, left(met(decided(run(0L, null), true),
                decided(run(0L, null), false))));
    }

    @Test
    void aWayThatComesOutOneWayWhereverIsDividedByNothing() {
        assertEquals(UNDIVIDED, left(decided(run(0L, null), true)));
    }

    /**
     * The age of the issue: a birthday from 1900 on is sixty only from 1960, so the way that
     * holds it has no row before 1960, and the way that fails it has one at every year. Met, the
     * years up to 1959 are a class of their own.
     */
    @Test
    void theYearsAWayThatHoldsTheAgeHasNoRowAtAreSettledByTheOtherWay() {
        EachWayItComesOut holding = decided(run(1960L, null), true);
        EachWayItComesOut failing = decided(run(1900L, null), false);

        assertEquals(settled(1900L, 1959L, false, 1900L, null), left(met(holding, failing)));
    }

    /** Meeting is a union: in either order, in either grouping, and of a way with itself. */
    @Test
    void meetingIsAUnion() {
        List<EachWayItComesOut> ways = List.of(decided(run(0L, null), true),
                decided(run(5L, null), false), decided(run(0L, 3L), false),
                decided(run(0L, 9L), run(2L, 7L), true, null), decided(run(1960L, null), true));
        for (EachWayItComesOut a : ways) {
            assertEquals(left(a), left(met(a, a)), a.toString());
            for (EachWayItComesOut b : ways) {
                assertEquals(left(met(a, b)), left(met(b, a)), a + " " + b);
                for (EachWayItComesOut c : ways) {
                    assertEquals(left(met(met(a, b), c)), left(met(a, met(b, c))),
                            a + " " + b + " " + c);
                }
            }
        }
    }

    /** What {@code way} shows of holding and of failing at {@code value}, or null where no
     *  stretch holds it. */
    private static List<EachWayItComesOut.Shown> shownAt(EachWayItComesOut way, long value) {
        ExactRatio at = ExactRatio.of(value);
        for (EachWayItComesOut.Stretch each : way.stretches()) {
            if (above(at, each.from()) && below(at, each.to())) {
                return List.of(each.holding(), each.failing());
            }
        }
        return null;
    }

    private static boolean above(ExactRatio at, ExactCut from) {
        return from == null || at.compareTo(from.at()) > 0
                || (from.inclusive() && at.compareTo(from.at()) == 0);
    }

    private static boolean below(ExactRatio at, ExactCut to) {
        return to == null || at.compareTo(to.at()) < 0
                || (to.inclusive() && at.compareTo(to.at()) == 0);
    }
}
