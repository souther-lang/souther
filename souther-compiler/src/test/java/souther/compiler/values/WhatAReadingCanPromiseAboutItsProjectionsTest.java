package souther.compiler.values;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reading may promise about the values it reports, which is two questions and not one.
 *
 * <p>What is held is one set per position, standing for the product of them. A choice between
 * alternatives written at two positions is a union of two products, and the smallest product holding
 * that union is the pair of unions — so the relation is lost there. The projections are not: the
 * projection of a union is the union of the projections, so what each position is reported as
 * holding is still exactly what the read rules leave it.
 *
 * <p>It is the next conjunction that spends what the choice lost. Two such readings are met one
 * position at a time, and a pair the two of them refuse between them is a pair neither intersection
 * can exclude — so the values come back wider than the rules are with every rule read.
 *
 * <p>Both are what this reading can prove and not what is true of the model. A conservative rule may
 * answer false where the values happen to be exact, which is why they are read as guarantees: what
 * they say holds, and what they do not say is unknown.
 */
class WhatAReadingCanPromiseAboutItsProjectionsTest {

    private static final String A = "a";
    private static final String B = "b";
    private static final Value FIVE = Value.text("5");
    private static final Value SIX = Value.text("6");
    private static final Value ZERO = Value.text("0");
    private static final Value ONE = Value.text("1");

    private static AdmissibleValues<String> says(String atom, Value value) {
        return AdmissibleValues.at(atom, ValueSet.just(value));
    }

    /** Both positions of one alternative, which is a product and is held as one. */
    private static AdmissibleValues<String> pair(Value a, Value b) {
        return says(A, a).meet(says(B, b));
    }

    /** A reading with nothing read is exact about everything it says, which is nothing. */
    @Test
    void aReadingThatSaysNothingPromisesBoth() {
        AdmissibleValues<String> nothing = AdmissibleValues.top();

        assertTrue(nothing.relationExact(), "an empty reading is the whole of what it read");
        assertTrue(nothing.projectionsExact(), "and every position of it is at ANY, exactly");
    }

    /** A choice whose alternatives are written at one position between them is a product, so the
     *  union of two of them is one and nothing is lost. */
    @Test
    void aChoiceAtOnePositionPromisesItsRelation() {
        AdmissibleValues<String> either = says(A, FIVE).join(says(A, SIX));

        assertEquals(ValueSet.oneOf(java.util.Set.of(FIVE, SIX)), either.at(A));
        assertTrue(either.relationExact(), "two values of one position are a product");
        assertTrue(either.projectionsExact());
    }

    /**
     * A choice reaching across two positions loses the relation and keeps the projections.
     *
     * <p>The witness of issue #877, read as far as its first invariant. {@code a} really is left
     * {@code 5} or {@code 6} by that clause alone, and reporting so is right; what is gone is which
     * {@code b} went with which.
     */
    @Test
    void aChoiceAcrossTwoPositionsKeepsItsProjectionsAndLosesItsRelation() {
        AdmissibleValues<String> one = pair(FIVE, ZERO).join(pair(SIX, ONE));

        assertEquals(ValueSet.oneOf(java.util.Set.of(FIVE, SIX)), one.at(A));
        assertEquals(ValueSet.oneOf(java.util.Set.of(ZERO, ONE)), one.at(B));
        assertTrue(one.projectionsExact(), "the projection of a union is the union of projections");
        assertFalse(one.relationExact(), "which b went with which a is what the product cannot say");
    }

    /**
     * And the conjunction of two of them can promise neither.
     *
     * <p>The whole witness of issue #877. Only {@code (a = 5, b = 0)} satisfies both invariants —
     * {@code (6, 1)} is refused by the second and {@code (6, 0)} by the first — so {@code a} is left
     * {@code 5} and nothing else, while the reading meets {@code {5, 6}} with {@code {5, 6}} at
     * {@code a} and comes back with both.
     */
    @Test
    void twoChoicesAcrossTwoPositionsMetTogetherPromiseNeither() {
        AdmissibleValues<String> one = pair(FIVE, ZERO).join(pair(SIX, ONE));
        AdmissibleValues<String> two = pair(FIVE, ZERO).join(pair(SIX, ZERO));

        AdmissibleValues<String> both = one.meet(two);

        assertEquals(ValueSet.oneOf(java.util.Set.of(FIVE, SIX)), both.at(A), "which is wider than the rules leave it");
        assertFalse(both.projectionsExact(), "so the reading may not say this is what a holds");
        assertFalse(both.relationExact());
    }

    /** A conjunction of readings that are each a product is a product, and says so. */
    @Test
    void aConjunctionOfProductsPromisesBoth() {
        AdmissibleValues<String> both = pair(FIVE, ZERO).meet(says(A, FIVE));

        assertTrue(both.relationExact(), "the intersection of two products is a product");
        assertTrue(both.projectionsExact());
    }

    /** A promise about the relation is a promise about the projections, never the other way. */
    @Test
    void promisingTheRelationIsPromisingTheProjections() {
        for (AdmissibleValues<String> each : java.util.List.<AdmissibleValues<String>>of(
                AdmissibleValues.top(),
                says(A, FIVE),
                says(A, FIVE).join(says(A, SIX)),
                pair(FIVE, ZERO).join(pair(SIX, ONE)),
                pair(FIVE, ZERO).join(pair(SIX, ONE)).meet(pair(FIVE, ZERO).join(pair(SIX, ZERO))))) {
            assertTrue(!each.relationExact() || each.projectionsExact(),
                    each + " promises its relation and not its projections");
        }
    }
}
