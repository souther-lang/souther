package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Place;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What a range gives up is a value the carrier holds, and it gives one up wherever it holds one.
 *
 * <p>Two halves of one answer. {@link Carrier#onTheGrid} is where a carrier says which places are
 * its own, and {@link Carrier#somethingInside} used not to ask it: a range reaching past an end of
 * the order came back with the count at its own far end, which is no value of anything, while the
 * value at the end of the order lay in the range and was never offered. A caller checking the grid
 * afterwards saw a refusal it could not tell from a range holding nothing — which is the shape a
 * search reports as having found no row where a row exists.
 *
 * <p>Measured on a pair of ranges that differ in one thing: whether the range runs past the end of
 * the order. An expectation on the second alone holds against the reading that lost the first.
 */
class ARangeGivesUpAValueTheCarrierHoldsTest {

    /**
     * A range straddling the start of an order gives up the value at that start.
     *
     * <p>A time of day is the carrier whose ends are near enough to write down: it runs from
     * midnight to a second before it, so a rule reaching below midnight is a rule anybody could
     * write. The same shape is every other stepping order's — a day count below the first date, an
     * ordinal below the first case — and the counts there are too large to read.
     */
    @Test
    void aRangeReachingPastTheStartOfAnOrderGivesUpTheValueAtIt() {
        assertEquals(Count.of(0), inside(Carrier.TIME, -100, 10),
                "midnight is in the range and is the first value the order has");
        assertEquals(Count.of(10), inside(Carrier.TIME, 10, 100),
                "and a range wholly inside the order starts where it starts");
    }

    /** The same at the far end, which is the other way the order can be run past. */
    @Test
    void aRangeReachingPastTheEndOfAnOrderGivesUpAValueInsideIt() {
        Place last = Carrier.TIME.extent().high().at();
        assertNotNull(Carrier.TIME.onTheGrid(
                        Carrier.TIME.somethingInside(Endpoint.inclusive(last), null)),
                "a range from the last second of the day upward holds that second");
    }

    /** An enumeration is the tightest order of all, and the one whose counts read like values. */
    @Test
    void anEnumerationIsRunPastTheSameWay() {
        Carrier stage = new Carrier.Ordinal(
                TypeSymbols.declared(new TypeKey("example.stage", "Stage")),
                List.of(TypeSymbols.declared(new TypeKey("example.stage", "Prospecting")),
                        TypeSymbols.declared(new TypeKey("example.stage", "Qualified")),
                        TypeSymbols.declared(new TypeKey("example.stage", "Won"))));

        assertEquals(Count.of(0), inside(stage, -5, 1), "the first case is in the range");
        assertEquals(Count.of(2), inside(stage, 2, 9), "and so is the last");
        assertNull(stage.somethingInside(
                        Endpoint.inclusive(Count.of(5)), Endpoint.inclusive(Count.of(9))),
                "while a range wholly past the last case holds no case at all");
    }

    /**
     * Every carrier that steps, held to the same thing at both ends of its order.
     *
     * <p>Written out rather than asserted of the one that showed it. What decides this is the
     * spacing and not which carrier it is, so a carrier added later is held here the way it is held
     * everywhere else about itself.
     */
    @Test
    void everySteppingCarrierGivesUpAValueItHoldsAtEitherEndOfItsOrder() {
        for (Carrier carrier : List.of(Carrier.WHOLE, Carrier.DATE, Carrier.MOMENT, Carrier.TIME,
                Carrier.INSTANT)) {
            OrderedInterval reaches = carrier.extent();
            for (Endpoint end : List.of(reaches.low(), reaches.high())) {
                Count at = (Count) end.at();
                // A range with the end of the order inside it and reaching well past it either way.
                Place offered = carrier.somethingInside(
                        Endpoint.inclusive(at.plus(-1000)), Endpoint.inclusive(at.plus(1000)));
                assertNotNull(offered, carrier + " at " + at);
                assertNotNull(carrier.onTheGrid(offered),
                        () -> carrier + " offered " + offered + ", which it does not hold");
            }
        }
    }

    private static Place inside(Carrier carrier, long low, long high) {
        Place offered = carrier.somethingInside(
                Endpoint.inclusive(Count.of(low)), Endpoint.inclusive(Count.of(high)));
        assertNotNull(offered, carrier + " [" + low + ", " + high + "]");
        assertNotNull(carrier.onTheGrid(offered),
                carrier + " offered " + offered + ", which it does not hold");
        return offered;
    }
}
