package souther.compiler.numeric;

import souther.compiler.numeric.NumericDomain.Bounds;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two questions a range answers about another range: what spans both of them, and whether one
 * holds the other.
 *
 * <p>Written apart from the domain because both are read where a walk from a seed is proved
 * (§invariant-discharge-reduction) and the answers turn on inclusivity, which a comparison of the
 * two numbers alone does not say. There is no meet beside them: a meet of two ranges can hold
 * nothing, and this record has no way to say so — an absent end here is every value that way, and
 * a range with neither end is one nothing was said about rather than one holding nothing.
 */
class ARangeSpansTwoAndSaysWhichHoldsTheOtherTest {

    private static Endpoint at(long n, boolean inclusive) {
        return new Endpoint(Count.of(BigDecimal.valueOf(n)), inclusive);
    }

    private static Bounds between(long low, long high) {
        return new Bounds(at(low, true), at(high, true));
    }

    @Test
    void aSpanReachesTheFurtherEndOfEachSide() {
        assertEquals(between(1, 9), Bounds.spanning(between(1, 4), between(3, 9)));
        assertEquals(between(1, 9), Bounds.spanning(between(3, 9), between(1, 4)));
    }

    /** An end nothing bounds holds every value that way, so a span with one has none. */
    @Test
    void anEndNothingBoundsSpansEverythingThatWay() {
        assertEquals(new Bounds(null, at(9, true)),
                Bounds.spanning(new Bounds(null, at(4, true)), between(3, 9)));
        assertEquals(new Bounds(at(1, true), null),
                Bounds.spanning(between(1, 4), new Bounds(at(3, true), null)));
    }

    /** At one number the reached end is the looser one, which is what the numbers alone do not say. */
    @Test
    void atOneNumberTheEndThatIsReachedIsTheLooser() {
        assertEquals(new Bounds(at(0, true), at(4, true)),
                Bounds.spanning(new Bounds(at(0, true), at(4, false)),
                        new Bounds(at(0, false), at(4, true))));
    }

    @Test
    void aRangeLiesWithinAWiderOne() {
        assertTrue(between(2, 3).liesWithin(between(1, 4)));
        assertTrue(between(1, 4).liesWithin(between(1, 4)));
        assertFalse(between(1, 4).liesWithin(between(2, 3)));
    }

    /** An end the wider range does not have holds everything that way; an end the narrower one does
     * not have is inside only where the wider has none either. */
    @Test
    void anAbsentEndIsWideAndNotNarrow() {
        assertTrue(between(1, 4).liesWithin(new Bounds(null, null)));
        assertTrue(new Bounds(null, at(4, true)).liesWithin(new Bounds(null, at(9, true))));
        assertFalse(new Bounds(null, at(4, true)).liesWithin(between(1, 9)));
    }

    /** A value at an end the wider range does not reach is not inside it. */
    @Test
    void anEndTheWiderRangeDoesNotReachIsOutsideIt() {
        assertFalse(new Bounds(at(0, true), at(4, true))
                .liesWithin(new Bounds(at(0, false), at(4, true))));
        assertTrue(new Bounds(at(0, false), at(4, true))
                .liesWithin(new Bounds(at(0, true), at(4, true))));
    }
}
