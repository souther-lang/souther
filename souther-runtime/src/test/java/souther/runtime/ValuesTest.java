package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import java.util.Set;

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

    /**
     * A foreign container may hold two elements the language calls one. Java's equality is finer
     * than the language's, so {@code {1.0, 1.00}} is two elements to a {@code HashSet} and one to
     * Souther — and a comparison that asks "is each of mine somewhere in yours" would let both of
     * them find the same element of yours and never notice what yours has that mine does not.
     */
    @Test
    void aForeignSetCannotSpendOneElementTwice() {
        Set<BigDecimal> two = new java.util.HashSet<>(
                List.of(new BigDecimal("1.0"), new BigDecimal("1.00")));
        Set<BigDecimal> oneAndTwo = new java.util.HashSet<>(
                List.of(new BigDecimal("1"), new BigDecimal("2")));
        assertEquals(2, two.size(), "Java calls them two; the language calls them one");
        assertFalse(Values.equal(two, oneAndTwo));
        assertFalse(Values.equal(oneAndTwo, two));
    }

    @Test
    void aForeignMapCannotSpendOneKeyTwice() {
        Map<BigDecimal, String> two = new java.util.LinkedHashMap<>();
        two.put(new BigDecimal("1.0"), "x");
        two.put(new BigDecimal("1.00"), "x");
        Map<BigDecimal, String> oneAndTwo = new java.util.LinkedHashMap<>();
        oneAndTwo.put(new BigDecimal("1"), "x");
        oneAndTwo.put(new BigDecimal("2"), "x");
        assertFalse(Values.equal(two, oneAndTwo));
        assertFalse(Values.equal(oneAndTwo, two));
    }

    /** A container Souther built, against a foreign one holding the same duplicate. */
    @Test
    void anOwnedSetCannotSpendOneElementTwiceEither() {
        Set<BigDecimal> foreign = new java.util.HashSet<>(
                List.of(new BigDecimal("1.0"), new BigDecimal("1.00")));
        Set<BigDecimal> owned = Sets.fromList(
                List.of(new BigDecimal("1"), new BigDecimal("2")));
        assertFalse(Values.equal(owned, foreign));
        assertFalse(Values.equal(foreign, owned));
    }

    /**
     * The invariant the whole of this class exists for, asked of every shape that reaches it: two
     * values this calls the same must hash the same. It is the half that goes wrong alone.
     */
    @Test
    void whateverThisCallsEqualItHashesTheSame() {
        List<Object> shapes = List.of(
                new BigDecimal("1.0"),
                List.of(new BigDecimal("1.0")),
                PersistentVector.from(List.of(new BigDecimal("1.0"))),
                new java.util.HashSet<>(List.of(new BigDecimal("1.0"), new BigDecimal("1.00"))),
                Sets.fromList(List.of(new BigDecimal("1.0"))),
                mapOf(new BigDecimal("1.0"), "x"),
                mapOf(new BigDecimal("1.0"), "y"),
                new java.util.HashSet<>(List.of(new BigDecimal("1"), new BigDecimal("2"))),
                Tuple.of(new BigDecimal("1.0"), "x"),
                "x",
                1L);
        List<Object> others = List.of(
                new BigDecimal("1"),
                PersistentVector.from(List.of(new BigDecimal("1"))),
                List.of(new BigDecimal("1.00")),
                Sets.fromList(List.of(new BigDecimal("1"))),
                new java.util.HashSet<>(List.of(new BigDecimal("1.00"))),
                mapOf(new BigDecimal("1"), "x"),
                mapOf(new BigDecimal("1.00"), "z"),
                Sets.fromList(List.of(new BigDecimal("1"), new BigDecimal("2"))),
                Tuple.of(new BigDecimal("1"), "x"),
                "y",
                2L);
        for (Object a : shapes) {
            for (Object b : others) {
                if (Values.equal(a, b)) {
                    assertEquals(Values.hash(a), Values.hash(b),
                            () -> "equal but hashed apart: " + a + " / " + b);
                }
            }
        }
    }

    private static Map<BigDecimal, String> mapOf(BigDecimal key, String value) {
        Map<BigDecimal, String> m = new java.util.LinkedHashMap<>();
        m.put(key, value);
        return m;
    }

    @Test
    void aNullDecimalIsAbsentRatherThanZero() {
        assertTrue(Values.equal((BigDecimal) null, (BigDecimal) null));
        assertFalse(Values.equal(null, new BigDecimal("0")));
        assertFalse(Values.equal(new BigDecimal("0"), null));
        assertEquals(0, Values.hash((BigDecimal) null));
    }
}
