package souther.runtime;

import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a collection holds is a number of the language (spec §what-a-collection-holds), and a
 * collection one element past it aborts rather than wrapping its size negative. Asked of
 * {@link Capacity} directly: a collection that full is two billion elements, which is not
 * something a test builds, and a test that builds a list to ask a bound says what the heap holds.
 */
class ACollectionHoldsAsManyAsItsSizeCountsTest {

    private static final long MOST = Capacity.MOST_ELEMENTS;

    @Test
    void theLastElementHasAPlaceAndTheOneAfterItDoesNot() {
        assertDoesNotThrow(() -> Capacity.oneMore((int) MOST - 1, "List"));
        assertThrows(ConstraintViolation.class, () -> Capacity.oneMore((int) MOST, "List"));
    }

    /** What the JVM has to be able to do for the bound to be the language's: count a size in an
     *  {@code int}. The number itself is the specification's, kept equal to it by a test of its
     *  own. */
    @Test
    void anIntSizeCanCountTheBound() {
        assertTrue(MOST <= Integer.MAX_VALUE);
    }

    @Test
    void aSpanIsMeasuredInTheElementsItWouldHold() {
        assertDoesNotThrow(() -> Capacity.span(0, MOST - 1));
        assertDoesNotThrow(() -> Capacity.span(Long.MIN_VALUE, Long.MIN_VALUE + MOST - 1));
        assertThrows(ConstraintViolation.class, () -> Capacity.span(0, MOST));
        assertThrows(ConstraintViolation.class, () -> Capacity.span(1, MOST + 1));
    }

    /** The width itself does not fit a {@code long}: it must not wrap into one that looks small. */
    @Test
    void aSpanWiderThanALongCountsIsAbortedAndNotWrapped() {
        assertThrows(ConstraintViolation.class, () -> Capacity.span(Long.MIN_VALUE, Long.MAX_VALUE));
        assertThrows(ConstraintViolation.class, () -> Capacity.span(-1, Long.MAX_VALUE));
        assertThrows(ConstraintViolation.class, () -> Capacity.span(0, Long.MAX_VALUE));
    }

    @Test
    void aSpanFromAboveToBelowIsEmptyBeforeAnyMeasure() {
        assertEquals(0, Lists.rangeInclusive(Long.MAX_VALUE, Long.MIN_VALUE + 1).size());
        assertEquals(0, Lists.rangeInclusive(1, 0).size());
    }

    @Test
    void anOrdinarySpanIsTheIntegersBothEndsIncluded() {
        assertEquals(List.of(-1L, 0L, 1L), Lists.rangeInclusive(-1, 1));
        assertEquals(List.of(5L), Lists.rangeInclusive(5, 5));
        assertThrows(ConstraintViolation.class, () -> Lists.rangeInclusive(0, MOST));
    }

    /** A walk over the leaves of a vector holding the most a collection holds ends on its last
     *  element: the last leaf is 31 slots, and a step of a whole leaf from its start would carry
     *  the position over the top of an {@code int}. Only the last two leaves are asked, in
     *  {@code int} arithmetic as a walk does it, because the step that carried over is the one
     *  from the last leaf and the leaves before it are all whole. Nothing is built. */
    @Test
    void aWalkOverTheLeavesOfTheFullestVectorEndsOnItsLastElement() {
        int cnt = (int) MOST;
        int last = ((cnt - 1) / 32) * 32;
        int beforeLast = last - 32;

        assertEquals(32, PersistentVector.leafLength(beforeLast, cnt));
        assertEquals(last, beforeLast + PersistentVector.leafLength(beforeLast, cnt));
        assertEquals(31, PersistentVector.leafLength(last, cnt));
        assertEquals(cnt, last + PersistentVector.leafLength(last, cnt));
    }
}
