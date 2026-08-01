package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Sameness for a Souther value. Scale is not part of a Decimal's identity, so equality ignores it
 * and the hash has to ignore it too: a value that compares equal and hashes differently lands in
 * another bucket and stops being findable by its own key.
 */
class ValuesTest {

    @Test
    void aDecimalIgnoresScale() {
        assertTrue(Values.equal(new BigDecimal("1.0"), new BigDecimal("1")));
        assertTrue(Values.equal(new BigDecimal("0.50"), new BigDecimal("0.5")));
        assertFalse(Values.equal(new BigDecimal("1.5"), new BigDecimal("1")));
    }

    @Test
    void theHashFollowsTheEquality() {
        assertEquals(Values.hash(new BigDecimal("1.0")), Values.hash(new BigDecimal("1")));
        assertEquals(Values.hash(new BigDecimal("0.00")), Values.hash(new BigDecimal("0")));
        assertEquals(Values.hash(new BigDecimal("10")), Values.hash(new BigDecimal("1E+1")));
    }

    @Test
    void aDecimalReachedThroughObjectIsTheSameAnswer() {
        Object a = new BigDecimal("1.0");
        Object b = new BigDecimal("1");
        assertTrue(Values.equal(a, b));
        assertEquals(Values.hash(a), Values.hash(b));
    }

    @Test
    void aValueThatCarriesItsOwnSemanticsIsAskedForThem() {
        List<BigDecimal> owned = PersistentVector.from(List.of(new BigDecimal("1.0")));
        List<BigDecimal> foreign = List.of(new BigDecimal("1"));
        assertTrue(Values.equal(owned, foreign));
        assertTrue(Values.equal(foreign, owned));   // either side may carry them
        assertEquals(Values.hash(owned), Values.hash(PersistentVector.from(foreign)));
    }

    @Test
    void aCarrierThatAnswersForItselfIsNotAskedTwice() {
        // a Long or a String is never the same value as a container, so answering from its own
        // equality is the same answer the ValueSemantics route would give, one test sooner
        List<String> anyContainer = PersistentVector.from(List.of("x"));
        assertFalse(Values.equal("x", anyContainer));
        assertFalse(Values.equal(1L, anyContainer));
    }

    @Test
    void anythingElseIsItsOwnEquality() {
        assertTrue(Values.equal("a", "a"));
        assertFalse(Values.equal("a", "b"));
        assertTrue(Values.equal(null, null));
        assertFalse(Values.equal(null, "a"));
        assertFalse(Values.equal("a", null));
        assertEquals(0, Values.hash(null));
        assertEquals("a".hashCode(), Values.hash("a"));
    }

    @Test
    void aNullDecimalIsAbsentRatherThanZero() {
        assertTrue(Values.equal((BigDecimal) null, (BigDecimal) null));
        assertFalse(Values.equal(null, new BigDecimal("0")));
        assertFalse(Values.equal(new BigDecimal("0"), null));
        assertEquals(0, Values.hash((BigDecimal) null));
    }
}
