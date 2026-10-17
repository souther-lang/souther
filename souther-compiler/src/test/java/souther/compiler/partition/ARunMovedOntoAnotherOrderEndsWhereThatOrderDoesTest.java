package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Towards;

import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A run of distances between two positions read as a run of places once the other position is
 * known, on an order that stops: four stages, at nought to three.
 *
 * <p>Each end the rules leave lands on a place, past one end of the order, or nowhere. Past the end
 * on the run's own outer side it reaches as far as the order does; past the far end the run holds
 * nothing there; nowhere leaves nothing to read.
 */
class ARunMovedOntoAnotherOrderEndsWhereThatOrderDoesTest {

    /** The run of distances from one to three. */
    private static final Band ONE_TO_THREE = new Band(
            new BandEnd.AtDomain(Bound.at(Level.OfTheQuantity.of(1), true)),
            new BandEnd.AtDomain(Bound.at(Level.OfTheQuantity.of(3), true)));

    /** Moved by {@code from} onto the four stages. */
    private static Function<Level, Band.Landing> from(long from) {
        return level -> {
            ExactRatio moved = level.asANumber().plus(ExactRatio.of(from)).orNull();
            if (moved.compareTo(ExactRatio.ZERO) < 0) {
                return new Band.Landing.PastTheEnd(Towards.BELOW);
            }
            if (moved.compareTo(ExactRatio.of(3)) > 0) {
                return new Band.Landing.PastTheEnd(Towards.ABOVE);
            }
            return new Band.Landing.On(new Level.OfTheQuantity(moved));
        };
    }

    @Test
    void bothEndsOnAPlaceAreMovedThere() {
        assertEquals(new Band(new BandEnd.AtDomain(Bound.at(Level.OfTheQuantity.of(1), true)),
                        new BandEnd.AtDomain(Bound.at(Level.OfTheQuantity.of(3), true))),
                ONE_TO_THREE.mappedBy(from(0)));
    }

    /** From the second stage the run is the last stage and past it: as far as the stages go. */
    @Test
    void anEndPastTheOrderOnItsOwnSideReachesAsFarAsTheOrderDoes() {
        assertEquals(new Band(new BandEnd.AtDomain(Bound.at(Level.OfTheQuantity.of(3), true)),
                        new BandEnd.AtOrderEnd(Towards.ABOVE)),
                ONE_TO_THREE.mappedBy(from(2)));
        assertEquals(new Band(new BandEnd.AtOrderEnd(Towards.BELOW),
                        new BandEnd.AtDomain(Bound.at(Level.OfTheQuantity.of(1), true))),
                ONE_TO_THREE.mappedBy(from(-2)));
    }

    /** From the last stage the run starts past it, and holds no stage. */
    @Test
    void anEndPastTheFarEndLeavesTheRunNothing() {
        assertNull(ONE_TO_THREE.mappedBy(from(3)));
        assertNull(ONE_TO_THREE.mappedBy(from(-4)));
    }

    @Test
    void anEndLandingNowhereLeavesNothingToRead() {
        assertNull(ONE_TO_THREE.mappedBy(level -> new Band.Landing.Nowhere()));
    }
}
