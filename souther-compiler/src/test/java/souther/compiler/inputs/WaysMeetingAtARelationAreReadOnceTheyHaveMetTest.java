package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
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
 * can ({@link EachWayItComesOut#eitherOf}). A way whose own statements decide the relation keeps
 * the rows it comes out that way at ({@link EachWayItComesOut#comingOut}), so a value it never
 * reaches takes nothing from it, and what the ways leave is read once they have met
 * ({@link EachWayItComesOut#leaves}).
 */
class WaysMeetingAtARelationAreReadOnceTheyHaveMetTest {

    private static NumericDomain.Bounds from(long least) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(least)), null);
    }

    private static final NumericDomain.Bounds EVERY = NumericDomain.Bounds.OPEN;

    private static EachWayItComesOut of(WhatARelationLeavesUndivided.Leaves leaves,
                                        NumericDomain.Bounds lies) {
        return EachWayItComesOut.of(leaves, lies, Granularity.DISCRETE);
    }

    /** Left either way at every value it lies at. */
    private static EachWayItComesOut either(NumericDomain.Bounds lies) {
        return of(new WhatARelationLeavesUndivided.Leaves.Undivided(), lies);
    }

    private static WhatARelationLeavesUndivided.Leaves settled(Long from, Long to, boolean holds) {
        return WhatARelationLeavesUndivided.Leaves.Settled.ofWhole(
                List.of(WhatARelationLeavesUndivided.SettledRun.whole(
                        from == null ? null : BigInteger.valueOf(from),
                        to == null ? null : BigInteger.valueOf(to), holds)), null, null);
    }

    /** A way the relation comes out {@code holds} along, at every value from {@code least}. */
    private static EachWayItComesOut decided(long least, boolean holds) {
        return either(from(least)).comingOut(holds);
    }

    private static EachWayItComesOut met(EachWayItComesOut... ways) {
        return EachWayItComesOut.eitherOf(List.of(ways));
    }

    private static WhatARelationLeavesUndivided.Leaves left(EachWayItComesOut ways) {
        return ways.leaves(Set.of(), Set.of());
    }

    private static final WhatARelationLeavesUndivided.Leaves UNDIVIDED =
            new WhatARelationLeavesUndivided.Leaves.Undivided();

    @Test
    void aWayThatComesOutOneWayWhereverIsDividedByNothing() {
        assertEquals(UNDIVIDED, left(decided(0, true)));
    }

    @Test
    void twoWaysThatComeOutTheSameWayComeOutThatWay() {
        assertEquals(UNDIVIDED, left(met(decided(0, true), decided(0, true))));
    }

    @Test
    void twoWaysThatComeOutTwoWaysAtTheSameValuesLeaveThemEitherWay() {
        assertEquals(UNDIVIDED, left(met(decided(0, true), decided(0, false))));
    }

    @Test
    void aValueLeftEitherWayByOneWayStaysSoBesideAWayThatComesOutOneWay() {
        assertEquals(UNDIVIDED, left(met(either(EVERY), decided(0, true))));
    }

    /** That every row at a value comes out one way says how a row there would come out, and not
     *  that there is one: two ways settling it two ways at a value do not show it either way. */
    @Test
    void aValueThatMayComeOutEitherWayAndIsNotShownToIsShownNothingOf() {
        assertNull(left(met(of(settled(null, 9L, false), EVERY),
                of(settled(null, 9L, true), EVERY))));
    }

    /**
     * The age of the issue: a birthday from 1900 on fails sixty at every year up to 1959 and leaves
     * it either way from 1960, along a way that decides nothing; along a way that holds it, read
     * without what decides it, no year before 1960 is one it holds at. Met, the years up to 1959 are
     * a class of their own.
     */
    @Test
    void theYearsAWayThatHoldsTheAgeNeverReachesAreSettledByTheOtherWay() {
        EachWayItComesOut open = of(settled(null, 1959L, false), EVERY);
        EachWayItComesOut holding = of(settled(null, 1959L, false), EVERY).comingOut(true);

        assertEquals(settled(null, 1959L, false), left(met(open, holding)));
    }

    /** Ways that each come out one way, on values the other never reaches, part the term where
     *  they meet. */
    @Test
    void waysComingOutTwoWaysOnValuesApartPartTheTerm() {
        EachWayItComesOut holdingFromOne = decided(1, true);
        EachWayItComesOut failingUpToNought = of(settled(1L, null, true), EVERY).comingOut(false);

        assertEquals(2, ((WhatARelationLeavesUndivided.Leaves.Settled) left(
                met(holdingFromOne, failingUpToNought))).runs().size());
    }

    /** Meeting is a union: in either order, in either grouping, and of a way with itself. */
    @Test
    void meetingIsAUnion() {
        List<EachWayItComesOut> ways = List.of(decided(0, true), decided(5, false),
                of(settled(null, 3L, false), EVERY), of(settled(null, 7L, true), EVERY),
                either(from(2)), either(EVERY),
                of(settled(null, 1959L, false), EVERY).comingOut(true));
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
}
