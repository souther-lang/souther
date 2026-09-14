package souther.compiler.check;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.regex.Meter;
import souther.compiler.values.ValueSet;
import souther.compiler.regex.PatternPlan;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A walk over a run of a stepping order starts at a place the run holds.
 *
 * <p>What makes the walk long enough is that it spends a step for each value it was told to keep
 * away from: a stretch that long holds a value none of them names. A strict end names a value the
 * run leaves out, so a walk anchored there spends its first step arriving — and a run whose values
 * were all held apart but one comes back empty, which reads as an order with nothing in it.
 */
class AWalkOverARunStartsAtAPlaceTheRunHoldsTest {

    private static Meter meter() {
        return PatternPlan.Budget.OF_A_WITNESS.meter();
    }

    private static Place inside(OrderedInterval run, Place... apart) {
        return Carrier.WHOLE.somewhereIn(ValueSet.ANY, run, PlacesApart.of(List.of(apart)),
                meter());
    }

    private static OrderedInterval above(long low, long high) {
        return new OrderedInterval(Endpoint.exclusive(Count.of(low)),
                Endpoint.inclusive(Count.of(high)));
    }

    @Test
    @DisplayName("the value beside a strict end is what a run above it begins at")
    void theRunBeginsBesideTheEndItIsNamedFor() {
        assertEquals(Count.of(4), inside(above(3, 5)));
    }

    @Test
    @DisplayName("and the one beyond it is reached once that one is held apart")
    void theNextValueIsReachedWithTheFirstHeldApart() {
        assertEquals(Count.of(5), inside(above(3, 5), Count.of(4)));
    }

    @Test
    @DisplayName("a run with only a strict end above it begins beside that end")
    void aRunBelowAStrictEndBeginsBesideIt() {
        OrderedInterval below = new OrderedInterval(null, Endpoint.exclusive(Count.of(3)));

        assertEquals(Count.of(2), inside(below));
        assertEquals(Count.of(1), inside(below, Count.of(2)));
    }

    @Test
    @DisplayName("a run holding one value gives it up and nothing else")
    void aRunOfOneValueGivesItUpAndNothingElse() {
        OrderedInterval one = new OrderedInterval(Endpoint.exclusive(Count.of(3)),
                Endpoint.exclusive(Count.of(5)));

        assertEquals(Count.of(4), inside(one));
        assertNull(inside(one, Count.of(4)),
                "the run holds one value and it is held apart, so there is none to give up");
    }

    @Test
    @DisplayName("a run two strict ends leave nothing between holds nothing")
    void aRunWithNothingBetweenItsEndsHoldsNothing() {
        assertNull(inside(new OrderedInterval(Endpoint.exclusive(Count.of(3)),
                        Endpoint.exclusive(Count.of(4)))),
                "no count lies between three and four");
    }
}
