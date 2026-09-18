package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a number this compiler worked out has to be for a carrier to hold a level at it.
 *
 * <p>Two things, and the number alone says only the first. It has to be a count at all — a third is
 * none — and it has to be a count this order stands at, which a half is not on the whole numbers.
 * Asked only the first, a level comes out saying it is a value of an order that has nothing there,
 * which is what {@link Level.OnACarrier}'s own account says it is not.
 *
 * <p><b>And off the grid is not the same answer as past the end.</b> {@link Carrier#onTheGrid} says
 * no to both, so a reader taking that answer alone refuses a line a model wrote: a size bound past
 * the whole numbers is one this compiler carries and names as unaccounted for. Only the first is
 * this compiler's own mistake, and only the first is refused.
 */
class AValueOfACarrierIsOffItsGridOrPastItsEndTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    private static ExactRatio ratio(long over, long under) {
        return ExactRatio.of(BigInteger.valueOf(over), BigInteger.valueOf(under));
    }

    /** A number the order stands at is the level, and the place is the count it is. */
    @Test
    void aNumberTheOrderStandsAtIsTheLevel() {
        assertEquals(new Level.OnACarrier(WHOLE, Count.of(4)),
                Level.OnACarrier.held(WHOLE, ExactRatio.of(4)));
    }

    /**
     * A count the order does not stand at is refused, which the number alone does not catch.
     *
     * <p>The discriminator between the two halves. A half is a finite decimal, so every reading
     * that stops at "is this a count" lets it through.
     */
    @Test
    void aCountTheOrderDoesNotStandAtIsRefused() {
        assertEquals(new Count(new BigDecimal("0.5")), Count.at(ratio(1, 2)),
                "a half is a count, which is the half of this a number can answer");

        assertThrows(IllegalStateException.class,
                () -> Level.OnACarrier.held(WHOLE, ratio(1, 2)),
                "and the whole numbers stand at none of them");
    }

    /**
     * And a count past where the order stops keeps its place.
     *
     * <p>Not this compiler's mistake but the model's, and one it is told about: a bound beyond the
     * whole numbers is carried to where a report names it as unaccounted for. Refused here, the
     * sentence a reader is owed would never be written.
     */
    @Test
    void aCountPastWhereTheOrderStopsIsCarried() {
        ExactRatio pastTheEnd = ExactRatio.of(BigInteger.valueOf(Long.MAX_VALUE)
                .add(BigInteger.ONE));

        assertEquals(new Level.OnACarrier(WHOLE, Count.at(pastTheEnd)),
                Level.OnACarrier.held(WHOLE, pastTheEnd));
    }
}
