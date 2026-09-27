package souther.runtime;

import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a collection holds is a number of the language (spec §what-a-collection-holds), and a
 * collection one element past it aborts rather than wrapping its size negative. Asked of
 * {@link Capacity} directly: a collection that full is two billion elements, which is not
 * something a test builds, and a test that builds a list to ask a bound says what the heap holds.
 */
class ACollectionHoldsAsManyAsItsSizeCountsTest {

    @Test
    void theLastElementHasAPlaceAndTheOneAfterItDoesNot() {
        assertDoesNotThrow(() -> Capacity.oneMore(Integer.MAX_VALUE - 1, "List"));
        assertThrows(ConstraintViolation.class, () -> Capacity.oneMore(Integer.MAX_VALUE, "List"));
    }

    @Test
    void theBoundIsTheOneAnIntSizeCountsTo() {
        assertEquals(Integer.MAX_VALUE, Capacity.MOST_ELEMENTS);
    }

    @Test
    void aSpanIsMeasuredInTheElementsItWouldHold() {
        long most = Capacity.MOST_ELEMENTS;
        assertDoesNotThrow(() -> Capacity.span(0, most - 1, most));
        assertDoesNotThrow(() -> Capacity.span(Long.MIN_VALUE, Long.MIN_VALUE + most - 1, most));
        assertThrows(ConstraintViolation.class, () -> Capacity.span(0, most, most));
        assertThrows(ConstraintViolation.class, () -> Capacity.span(1, most + 1, most));
    }

    /** The width itself does not fit a {@code long}: it must not wrap into one that looks small. */
    @Test
    void aSpanWiderThanALongCountsIsAbortedAndNotWrapped() {
        assertThrows(ConstraintViolation.class,
                () -> Capacity.span(Long.MIN_VALUE, Long.MAX_VALUE, Capacity.MOST_ELEMENTS));
        assertThrows(ConstraintViolation.class,
                () -> Capacity.span(-1, Long.MAX_VALUE, Capacity.MOST_ELEMENTS));
        assertThrows(ConstraintViolation.class,
                () -> Capacity.span(0, Long.MAX_VALUE, Capacity.MOST_ELEMENTS));
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
        assertThrows(ConstraintViolation.class,
                () -> Lists.rangeInclusive(0, Capacity.MOST_ELEMENTS));
    }
}
