package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedRuns;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.ValueSet;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a caller composing a value is handed keeps what the order leaves the position, whatever the
 * meet with where the value stops comes to.
 *
 * <p>Runs apart met with a range may come to one run or none. One run is where the value stops and
 * the runs to choose in are that run; none is a position nothing is offered at, and not the range
 * it was met with.
 */
class WhatTheOrderLeavesAPositionIsKeptThroughTheMeetTest {

    /** Every whole number below nought, or above a hundred. */
    private static final OrderedRuns APART = OrderedRuns.of(List.of(
            new OrderedInterval(null, Endpoint.inclusive(Count.of(-1))),
            new OrderedInterval(Endpoint.inclusive(Count.of(101)), null)));

    private static NumericDomain.Bounds from(long low, long high) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(low)),
                Endpoint.inclusive(Count.of(high)));
    }

    private static FieldDomains.ConstructionLimits limits(NumericDomain.Bounds values) {
        return FieldDomains.ConstructionLimits.of(values, APART, null,
                AdmissibleSet.complete(ValueSet.ANY), HeldClass.NONE);
    }

    @Test
    void bothRunsAreChosenInWhereTheRangeReachesBoth() {
        FieldDomains.ConstructionLimits both = limits(from(-10, 110));

        assertEquals(List.of(from(-10, -1), from(101, 110)), both.runs());
        assertEquals(from(-10, 110), both.values());
        assertFalse(both.leavesNothing());
    }

    @Test
    void oneRunLeftIsWhereTheValueStops() {
        FieldDomains.ConstructionLimits one = limits(from(0, 150));

        assertEquals(from(101, 150), one.values(), "the run, and not the range it was met with");
        assertEquals(List.of(from(101, 150)), one.runs());
    }

    @Test
    void noRunLeftLeavesNothingToChooseIn() {
        FieldDomains.ConstructionLimits none = limits(from(0, 100));

        assertTrue(none.leavesNothing());
        assertEquals(List.of(), none.runs(), "nothing to choose in, and not the range");
    }

    @Test
    void aPositionNoRuleOfTheOrderStopsIsChosenInWhereTheValueStops() {
        FieldDomains.ConstructionLimits open = FieldDomains.ConstructionLimits.of(from(0, 100),
                null, null, AdmissibleSet.complete(ValueSet.ANY), HeldClass.NONE);

        assertEquals(List.of(from(0, 100)), open.runs());
        assertFalse(open.leavesNothing());
    }
}
