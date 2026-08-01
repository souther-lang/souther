package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A tuple carries several values through a computation and compares by them, so two built separately
 * from the same values are one value. Its elements are Souther values, so an amount inside one
 * ignores its scale here as it does anywhere else.
 */
class TupleTest {

    @Test
    void twoTuplesOfTheSameValuesAreEqual() {
        assertEquals(Tuple.of("x", "y"), Tuple.of("x", "y"));
        assertEquals(Tuple.of("x", "y").hashCode(), Tuple.of("x", "y").hashCode());
    }

    @Test
    void differentValuesAreDifferentTuples() {
        assertNotEquals(Tuple.of("x", "y"), Tuple.of("x", "z"));
        assertNotEquals(Tuple.of("x", "y"), Tuple.of("x", "y", "z"));
        assertNotEquals(Tuple.of("x", "y"), "not a tuple");
    }

    @Test
    void anAmountInsideOneIgnoresItsScale() {
        assertEquals(Tuple.of(new BigDecimal("1.0"), "x"), Tuple.of(new BigDecimal("1"), "x"));
        assertEquals(Tuple.of(new BigDecimal("1.0"), "x").hashCode(),
                Tuple.of(new BigDecimal("1"), "x").hashCode());
    }

    @Test
    void aContainerInsideOneIsCompareByWhatItHolds() {
        assertEquals(Tuple.of(PersistentVector.from(List.of(new BigDecimal("1.0"))), "x"),
                Tuple.of(List.of(new BigDecimal("1")), "x"));
    }

    @Test
    void aTupleIsFoundInASet() {
        assertEquals(1, Sets.fromList(List.of(Tuple.of("x", "y"), Tuple.of("x", "y"))).size());
        assertTrue(Sets.contains(Tuple.of("x", "y"),
                Sets.fromList(List.of(Tuple.of("x", "y")))));
    }

    @Test
    void aTupleKeysAMap() {
        PersistentHashMap<Tuple, String> m =
                PersistentHashMap.<Tuple, String>empty().assoc(Tuple.of("a", "b"), "v");
        assertEquals("v", m.get(Tuple.of("a", "b")));
    }

    @Test
    void anElementIsReadByItsIndex() {
        Tuple t = Tuple.of("x", "y");
        assertEquals("x", t.get(0));
        assertEquals("y", t.get(1));
        assertEquals(2, t.size());
        assertEquals("(x, y)", t.toString());
    }

    @Test
    void ofIsNotDisturbedByAWriteToTheArrayItWasGiven() {
        Object[] xs = {"x", "y", "z"};
        Tuple t = Tuple.of(xs);
        int before = t.hashCode();
        xs[0] = "w";
        assertEquals(before, t.hashCode());
        assertEquals("x", t.get(0));
    }
}
