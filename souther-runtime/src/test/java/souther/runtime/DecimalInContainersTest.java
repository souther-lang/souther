package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A container decides sameness the way the language does, and keeps the Java contract it owes the
 * interface it implements. A Decimal is the one carrier whose own equality disagrees with the
 * language, and it must not survive being put in one.
 */
class DecimalInContainersTest {

    private static final BigDecimal ONE_SCALED = new BigDecimal("1.0");
    private static final BigDecimal ONE = new BigDecimal("1");

    @Test
    void aSetHoldsOneOfThem() {
        Set<BigDecimal> s = Sets.fromList(List.of(ONE_SCALED, ONE));
        assertEquals(1, s.size());
        assertTrue(Sets.contains(ONE, s));
        assertTrue(Sets.contains(ONE_SCALED, s));
    }

    @Test
    void aMapFindsItsValueByEitherScale() {
        PersistentHashMap<BigDecimal, String> m =
                PersistentHashMap.<BigDecimal, String>empty().assoc(ONE_SCALED, "yes");
        assertEquals("yes", m.get(ONE));
        assertTrue(m.containsKey(ONE));
    }

    @Test
    void twoListsOfTheSameAmountsAreOneValue() {
        PersistentVector<BigDecimal> a = PersistentVector.from(List.of(ONE_SCALED));
        PersistentVector<BigDecimal> b = PersistentVector.from(List.of(ONE));
        assertTrue(Values.equal(a, b));
        assertEquals(Values.hash(a), Values.hash(b));
    }

    @Test
    void aListKeepsTheJavaContractItOwesTheListInterface() {
        PersistentVector<BigDecimal> a = PersistentVector.from(List.of(ONE_SCALED));
        List<BigDecimal> jdk = List.of(ONE);
        assertEquals(jdk.equals(a), a.equals(jdk));   // symmetry, whichever way it answers
        assertNotEquals(a, jdk);                      // BigDecimal.equals says no, and both agree
    }

    @Test
    void aSetsEqualityFollowsTheMembershipItIsIndexedBy() {
        // one index, so `contains` is the language's and `equals` and `hashCode` follow it: a set
        // that found an element and hashed as though it had not would be equal to one it hashes apart
        Set<BigDecimal> a = Sets.fromList(List.of(ONE_SCALED));
        Set<BigDecimal> b = Sets.fromList(List.of(ONE));
        assertTrue(a.contains(ONE));
        assertEquals(a, b);
        assertEquals(a.hashCode(), b.hashCode());
    }

    @Test
    void aMapsEqualityFollowsTheLookupItIsIndexedBy() {
        PersistentHashMap<BigDecimal, String> a =
                PersistentHashMap.<BigDecimal, String>empty().assoc(ONE_SCALED, "v");
        PersistentHashMap<BigDecimal, String> b =
                PersistentHashMap.<BigDecimal, String>empty().assoc(ONE, "v");
        assertEquals(a, b);
        assertEquals(a.hashCode(), b.hashCode());
    }

    @Test
    void twoOptionalsOfTheSameAmountAreEqual() {
        Option<BigDecimal> a = new Option.Some<>(ONE_SCALED);
        Option<BigDecimal> b = new Option.Some<>(ONE);
        assertEquals(a, b);
        assertEquals(a.hashCode(), b.hashCode());
    }

    @Test
    void aListOfAmountsIsFoundInsideASet() {
        Set<List<BigDecimal>> s = Sets.fromList(List.of(
                PersistentVector.from(List.of(ONE_SCALED)),
                PersistentVector.from(List.of(ONE))));
        assertEquals(1, s.size());
    }

    @Test
    void aSetAndAMapAreThemselvesValues() {
        Set<BigDecimal> sa = Sets.fromList(List.of(ONE_SCALED));
        Set<BigDecimal> sb = Sets.fromList(List.of(ONE));
        assertTrue(Values.equal(sa, sb));
        assertEquals(Values.hash(sa), Values.hash(sb));

        PersistentHashMap<String, BigDecimal> ma =
                PersistentHashMap.<String, BigDecimal>empty().assoc("k", ONE_SCALED);
        PersistentHashMap<String, BigDecimal> mb =
                PersistentHashMap.<String, BigDecimal>empty().assoc("k", ONE);
        assertTrue(Values.equal(ma, mb));
        assertEquals(Values.hash(ma), Values.hash(mb));
    }

    @Test
    void aMapKeyedByAnAmountIsItselfAValue() {
        PersistentHashMap<BigDecimal, String> ma =
                PersistentHashMap.<BigDecimal, String>empty().assoc(ONE_SCALED, "v");
        PersistentHashMap<BigDecimal, String> mb =
                PersistentHashMap.<BigDecimal, String>empty().assoc(ONE, "v");
        assertTrue(Values.equal(ma, mb));
        assertEquals(Values.hash(ma), Values.hash(mb));
    }

    /**
     * A probe reads the container it was given, by the index that container carries. Every set
     * Souther builds — including the one a {@code Set} field decodes into — is indexed by the
     * language, so the amount is found at either scale. A {@code java.util.Set} handed in from Java
     * carries Java's index, and rebuilding it to ask would cost the whole set on every membership
     * test while buying nothing at the boundary, where a key or element is a String, a temporal or
     * an enumeration and the two indexes agree.
     */
    @Test
    void aProbeReadsTheIndexTheContainerCarries() {
        Set<BigDecimal> owned = Sets.fromList(List.of(ONE_SCALED));
        assertTrue(Sets.contains(ONE, owned));
        assertEquals(0, Sets.remove(ONE, owned).size());

        Set<BigDecimal> foreign = new HashSet<>(List.of(ONE_SCALED));
        assertFalse(Sets.contains(ONE, foreign));
    }

    /** Comparing two containers is a different question from probing one, and there both sides are
     *  normalized: a foreign set is a value here, not an index being read. */
    @Test
    void comparingAForeignSetStillAnswersTheLanguagesWay() {
        Set<BigDecimal> foreign = new HashSet<>(List.of(ONE_SCALED));
        Set<BigDecimal> owned = Sets.fromList(List.of(ONE));
        assertTrue(Values.equal(foreign, owned));
        assertEquals(Values.hash(foreign), Values.hash(owned));
    }
}
