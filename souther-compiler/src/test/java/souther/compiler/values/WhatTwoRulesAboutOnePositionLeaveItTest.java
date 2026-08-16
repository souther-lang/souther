package souther.compiler.values;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The values one position is left, rule by rule.
 *
 * <p>Two shapes carry every answer: the values a rule names, and the values it takes away. What is
 * asserted here is that the connectives keep them closed — no pair of rules leaves an answer neither
 * shape can hold — and that emptiness is reached only where values were counted.
 */
class WhatTwoRulesAboutOnePositionLeaveItTest {

    private static final Value A = Value.text("A");
    private static final Value B = Value.text("B");
    private static final Value C = Value.text("C");

    /** Two equalities naming different values leave nothing, which is the whole of the refusal. */
    @Test
    void twoEqualitiesNamingDifferentValuesLeaveNothing() {
        assertTrue(ValueSet.just(A).meet(ValueSet.just(B)).isEmpty());
    }

    /** And naming the same value they leave it. */
    @Test
    void twoEqualitiesNamingOneValueLeaveIt() {
        assertEquals(ValueSet.just(A), ValueSet.just(A).meet(ValueSet.just(A)));
    }

    /** An equality and its denial leave nothing. */
    @Test
    void anEqualityAndItsDenialLeaveNothing() {
        assertTrue(ValueSet.just(A).meet(ValueSet.allBut(A)).isEmpty());
    }

    /** A denial takes its value out of what an equality named, and leaves the rest. */
    @Test
    void aDenialTakesItsValueOutOfWhatWasNamed() {
        assertEquals(ValueSet.just(A),
                ValueSet.oneOf(Set.of(A, B)).meet(ValueSet.allBut(B)));
    }

    /**
     * Two denials over a carrier whose values are not counted out leave everything but the two.
     *
     * <p>Never nothing. What it would take to reach nothing is the values of the carrier in hand,
     * and where they are in hand the denial was turned into what it leaves before it got here.
     */
    @Test
    void twoDenialsLeaveEverythingButBoth() {
        ValueSet left = ValueSet.allBut(A).meet(ValueSet.allBut(B));
        assertEquals(new ValueSet.Cofinite(Set.of(A, B)), left);
        assertFalse(left.isEmpty());
    }

    /** Alternatives are the values either names. */
    @Test
    void twoEqualitiesAsAlternativesLeaveBoth() {
        assertEquals(ValueSet.oneOf(Set.of(A, B)), ValueSet.just(A).join(ValueSet.just(B)));
    }

    /** An alternative to a denial no longer denies what the other side names. */
    @Test
    void anAlternativeToADenialTakesBackWhatItNames() {
        assertEquals(ValueSet.ANY, ValueSet.just(A).join(ValueSet.allBut(A)));
        assertEquals(ValueSet.allBut(B), ValueSet.just(A).join(ValueSet.allBut(B)),
                "and leaves the denial of a value neither side names standing");
    }

    /** Two denials as alternatives deny only what both deny. */
    @Test
    void twoDenialsAsAlternativesDenyOnlyWhatBothDeny() {
        assertEquals(ValueSet.allBut(A),
                new ValueSet.Cofinite(Set.of(A, B)).join(new ValueSet.Cofinite(Set.of(A, C))));
    }

    /** Anything is what a position nothing was said about holds, and saying nothing twice says
     * nothing. */
    @Test
    void sayingNothingLeavesEverything() {
        assertTrue(ValueSet.ANY.isAny());
        assertTrue(ValueSet.ANY.meet(ValueSet.ANY).isAny());
        assertTrue(ValueSet.ANY.join(ValueSet.just(A)).isAny());
        assertEquals(ValueSet.just(A), ValueSet.ANY.meet(ValueSet.just(A)));
    }

    /** Nothing admitted stays nothing under a further rule, and takes an alternative's values. */
    @Test
    void nothingAdmittedIsNotWidenedByAFurtherRule() {
        assertTrue(ValueSet.NONE.meet(ValueSet.just(A)).isEmpty());
        assertEquals(ValueSet.just(A), ValueSet.NONE.join(ValueSet.just(A)));
    }

    /**
     * Two writings of one number are one value.
     *
     * <p>Which is what the interval algebra beside this already does with them: a declaration whose
     * rules name {@code 1.0m} and {@code 1.00m} is admitted, and one naming {@code 1.0m} and
     * {@code 2.0m} is refused. Two domains disagreeing here would leave one position holding two
     * sets of values.
     */
    @Test
    void twoWritingsOfOneNumberAreOneValue() {
        Value once = Value.number(new BigDecimal("1.0"));
        Value again = Value.number(new BigDecimal("1.00"));
        assertEquals(once, again);
        assertEquals(ValueSet.just(once), ValueSet.just(once).meet(ValueSet.just(again)));
        assertTrue(ValueSet.just(once).meet(ValueSet.just(Value.number(2))).isEmpty());
    }

    /** And a whole number written as one is the same value as the decimal it equals, so that a
     * position read through either spelling holds one set of values. */
    @Test
    void aWholeNumberIsTheNumberItEquals() {
        assertEquals(Value.number(1), Value.number(new BigDecimal("1.000")));
    }
}
