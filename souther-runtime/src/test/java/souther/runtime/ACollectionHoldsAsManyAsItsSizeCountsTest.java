package souther.runtime;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A collection one element past what its {@code int} size counts aborts rather than wrapping the
 * size negative. Asked of {@link Capacity} directly: a collection that full is two billion
 * elements, which is not something a test builds.
 */
class ACollectionHoldsAsManyAsItsSizeCountsTest {

    @Test
    void theLastElementHasAPlaceAndTheOneAfterItDoesNot() {
        assertDoesNotThrow(() -> Capacity.oneMore(Integer.MAX_VALUE - 1, "List"));
        assertThrows(ConstraintViolation.class, () -> Capacity.oneMore(Integer.MAX_VALUE, "List"));
    }
}
