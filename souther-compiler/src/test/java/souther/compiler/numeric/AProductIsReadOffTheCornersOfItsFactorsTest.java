package souther.compiler.numeric;

import souther.compiler.numeric.NumericDomain.Bounds;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What a product of two ranges is, asked of the ranges alone.
 *
 * <p>Held here rather than through the discharge check, which is fail-open: a bound this never
 * derived and a bound it derived wrongly both arrive as a warning nobody sees. Both directions are
 * pinned — a range wider than the true one proves less and is sound, a narrower one rejects a
 * program that is correct — and so is whether an end is one the product reaches, since that is what
 * a strict guard decides and what nothing downstream would notice moving.
 */
class AProductIsReadOffTheCornersOfItsFactorsTest {

    private static Bounds between(Long min, Long max) {
        return new Bounds(min == null ? null : Endpoint.inclusive(Count.of(min)),
                max == null ? null : Endpoint.inclusive(Count.of(max)));
    }

    private static Bounds above(long min, boolean reached) {
        return new Bounds(new Endpoint(Count.of(min), reached), null);
    }

    private static Count at(Endpoint end) {
        return (Count) end.at();
    }

    /** Two factors nothing is below is a product nothing is below — the whole of what the issue's
     * first example needs. */
    @Test
    void twoFactorsAtOrAboveZeroMakeAProductAtOrAboveZero() {
        Bounds product = Intervals.product(above(0, true), above(0, true));

        assertEquals(Count.of(0), at(product.min()));
        assertEquals(true, product.min().inclusive());
        assertNull(product.max(), "nothing bounds either factor above");
    }

    /** Both ends of both factors, so every corner is a number and the answer is the two furthest. */
    @Test
    void aProductLiesBetweenTheLeastAndGreatestOfItsCorners() {
        Bounds product = Intervals.product(between(-3L, 2L), between(-5L, 4L));

        assertEquals(Count.of(-12), at(product.min()), "-3 * 4");
        assertEquals(Count.of(15), at(product.max()), "-3 * -5");
    }

    /**
     * One end reaches what two corners land on, so a factor open at one of them does not make the
     * product open there.
     *
     * <p>{@code (-1, 1] * [-1, 1]} is at 1 both by {@code 1 * 1} and by {@code -1 * -1}, and only
     * the second corner is a pair of values the factors have. Read off whichever corner came first,
     * the product would be open at an end it reaches — and a clause of {@code value <= 1} would be
     * left owed where the guards settle it.
     */
    @Test
    void anEndTwoCornersLandOnIsReachedWhereEitherOfThemIs() {
        Bounds openBelow = new Bounds(new Endpoint(Count.of(-1), false),
                Endpoint.inclusive(Count.of(1)));

        Bounds product = Intervals.product(openBelow, between(-1L, 1L));

        assertEquals(Count.of(1), at(product.max()));
        assertEquals(true, product.max().inclusive(), "1 * 1 reaches it though -1 is not a value");
    }

    /** A factor that is only ever zero is a product that is only ever zero, whatever the other
     * factor ranges over. */
    @Test
    void zeroTimesAnythingIsZero() {
        Bounds product = Intervals.product(between(0L, 0L), new Bounds(null, null));

        assertEquals(Count.of(0), at(product.min()));
        assertEquals(Count.of(0), at(product.max()));
        assertEquals(true, product.min().inclusive());
        assertEquals(true, product.max().inclusive());
    }

    /**
     * A factor that only ever approaches zero, times one that is only ever zero, is at zero and
     * reaches it: every value the first one takes times zero is zero.
     *
     * <p>The end an open factor contributes is not what decides this, which is what taking the
     * strictness of both ends would have said.
     */
    @Test
    void aFactorThatOnlyApproachesZeroStillReachesZeroTimesZero() {
        Bounds product = Intervals.product(above(0, false), between(0L, 0L));

        assertEquals(Count.of(0), at(product.max()));
        assertEquals(true, product.max().inclusive());
        assertEquals(Count.of(0), at(product.min()));
        assertEquals(true, product.min().inclusive());
    }

    /** Two factors that only approach zero make a product that only approaches it. */
    @Test
    void twoFactorsThatOnlyApproachZeroLeaveAProductThatDoesNotReachIt() {
        Bounds product = Intervals.product(above(0, false), above(0, false));

        assertEquals(Count.of(0), at(product.min()));
        assertEquals(false, product.min().inclusive());
        assertNull(product.max());
    }

    /** Nothing bounds a factor above and nothing bounds the other below, so the product runs past
     * every value both ways. */
    @Test
    void twoUnboundedFactorsBoundNothing() {
        Bounds product = Intervals.product(new Bounds(null, null), new Bounds(null, null));

        assertNull(product.min());
        assertNull(product.max());
    }

    /** Two factors nothing is above is a product nothing is above, and the corner where the two
     * unbounded ends meet is what says so. */
    @Test
    void aProductOfTwoRangesBoundedOnlyBelowIsBoundedOnlyBelow() {
        Bounds product = Intervals.product(above(2, true), above(3, true));

        assertEquals(Count.of(6), at(product.min()));
        assertNull(product.max());
    }

    /** Both factors at or below zero, so the product is at or above zero — the corner where two
     * ends past every value meet is the one that decides it. */
    @Test
    void twoFactorsAtOrBelowZeroMakeAProductAtOrAboveZero() {
        Bounds atMostZero = new Bounds(null, Endpoint.inclusive(Count.of(0)));

        Bounds product = Intervals.product(atMostZero, atMostZero);

        assertEquals(Count.of(0), at(product.min()));
        assertEquals(true, product.min().inclusive());
        assertNull(product.max());
    }
}
