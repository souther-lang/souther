package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;

import java.math.BigInteger;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A witness holds a container at a count only where some row does: the fewest count from where it
 * is asked that the run of how many the container holds takes, both of its ends read as the ends
 * they are. An end the run stops short of is a count it does not take.
 */
class AContainerIsHeldOnlyAtACountSomeRowTakesTest {

    private static NumericDomain.Bounds run(Endpoint min, Endpoint max) {
        return new NumericDomain.Bounds(min, max);
    }

    private static Endpoint at(long count) {
        return Endpoint.inclusive(Count.of(count));
    }

    private static Endpoint shortOf(long count) {
        return Endpoint.exclusive(Count.of(count));
    }

    private static Optional<BigInteger> fewest(NumericDomain.Bounds held, long from) {
        return UndividedByARelation.fewestTakenFrom(held, BigInteger.valueOf(from));
    }

    @Test
    void aRunThatStopsShortOfOneTakesNoEntry() {
        assertEquals(Optional.empty(), fewest(run(at(0), shortOf(1)), 1));
        assertEquals(Optional.of(BigInteger.ZERO), fewest(run(at(0), shortOf(1)), 0));
    }

    @Test
    void aRunThatStopsShortOfTheCountAskedTakesNone() {
        assertEquals(Optional.empty(), fewest(run(at(0), shortOf(3)), 3));
        assertEquals(Optional.of(BigInteger.TWO), fewest(run(at(0), at(2)), 2));
    }

    /** Past nought and short of one is a run with values between its ends and no count. */
    @Test
    void aRunBetweenTwoCountsItStopsShortOfTakesNeither() {
        assertEquals(Optional.empty(), fewest(run(shortOf(0), shortOf(1)), 0));
    }

    @Test
    void theFewestIsTheFirstCountTheRunTakesFromWhereItIsAsked() {
        assertEquals(Optional.of(BigInteger.TWO), fewest(run(at(2), null), 1));
        assertEquals(Optional.of(BigInteger.ONE), fewest(run(shortOf(0), at(4)), 0));
        assertEquals(Optional.of(BigInteger.valueOf(3)), fewest(run(null, null), 3));
    }

    @Test
    void aRunHoldingNothingOrNotWorkedOutTakesNoCount() {
        assertEquals(Optional.empty(), fewest(run(at(0), at(0)), 1));
        assertEquals(Optional.empty(), fewest(run(at(3), at(2)), 0));
        assertEquals(Optional.empty(), fewest(null, 0));
    }
}
