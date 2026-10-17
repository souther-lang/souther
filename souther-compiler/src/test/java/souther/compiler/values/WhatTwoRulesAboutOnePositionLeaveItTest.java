package souther.compiler.values;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
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
 *
 * <p>Put together by {@link Allowance}, which is where two of them are put together. Every set below is
 * values written out, so nothing is built and the allowance is never touched — what is being read
 * is the arithmetic.
 */
class WhatTwoRulesAboutOnePositionLeaveItTest {

    private static final Sameness.Block<String> POSITION = Sameness.Block.of("value");
    private static final Value A = Value.text("A");
    private static final Value B = Value.text("B");
    private static final Value C = Value.text("C");

    private final Allowance<String> sets = AsACompilationAllows.forAdmittedValues();

    /** What both leave, read as the set it is. */
    private ValueSet met(ValueSet one, ValueSet other) {
        return sets.meet(POSITION, one, other).set();
    }

    /** And what either leaves, said as one plan over the alternatives — which is how a block holds
     *  what its alternatives leave it. */
    private ValueSet joined(ValueSet one, ValueSet other) {
        return sets.joining(POSITION, List.of(one, other)).set();
    }

    /** Two equalities naming different values leave nothing, which is the whole of the refusal. */
    @Test
    void twoEqualitiesNamingDifferentValuesLeaveNothing() {
        assertTrue(met(ValueSet.just(A), ValueSet.just(B)).isEmpty());
    }

    /** And naming the same value they leave it. */
    @Test
    void twoEqualitiesNamingOneValueLeaveIt() {
        assertEquals(ValueSet.just(A), met(ValueSet.just(A), ValueSet.just(A)));
    }

    /** An equality and its denial leave nothing. */
    @Test
    void anEqualityAndItsDenialLeaveNothing() {
        assertTrue(met(ValueSet.just(A), ValueSet.allBut(A)).isEmpty());
    }

    /** A denial takes its value out of what an equality named, and leaves the rest. */
    @Test
    void aDenialTakesItsValueOutOfWhatWasNamed() {
        assertEquals(ValueSet.just(A), met(ValueSet.oneOf(Set.of(A, B)), ValueSet.allBut(B)));
    }

    /**
     * Two denials over a carrier whose values are not counted out leave everything but the two.
     *
     * <p>Never nothing. What it would take to reach nothing is the values of the carrier in hand,
     * and where they are in hand the denial was turned into what it leaves before it got here.
     */
    @Test
    void twoDenialsLeaveEverythingButBoth() {
        ValueSet left = met(ValueSet.allBut(A), ValueSet.allBut(B));
        assertEquals(new ValueSet.Cofinite(Set.of(A, B)), left);
        assertFalse(left.isEmpty());
    }

    /** Alternatives are the values either names. */
    @Test
    void twoEqualitiesAsAlternativesLeaveBoth() {
        assertEquals(ValueSet.oneOf(Set.of(A, B)), joined(ValueSet.just(A), ValueSet.just(B)));
    }

    /** An alternative to a denial no longer denies what the other side names. */
    @Test
    void anAlternativeToADenialTakesBackWhatItNames() {
        assertEquals(ValueSet.ANY, joined(ValueSet.just(A), ValueSet.allBut(A)));
        assertEquals(ValueSet.allBut(B), joined(ValueSet.just(A), ValueSet.allBut(B)),
                "and leaves the denial of a value neither side names standing");
    }

    /** Two denials as alternatives deny only what both deny. */
    @Test
    void twoDenialsAsAlternativesDenyOnlyWhatBothDeny() {
        assertEquals(ValueSet.allBut(A), joined(new ValueSet.Cofinite(Set.of(A, B)),
                new ValueSet.Cofinite(Set.of(A, C))));
    }

    /** Anything is what a position nothing was said about holds, and saying nothing twice says
     * nothing. */
    @Test
    void sayingNothingLeavesEverything() {
        assertTrue(ValueSet.ANY.isAny());
        assertTrue(met(ValueSet.ANY, ValueSet.ANY).isAny());
        assertTrue(joined(ValueSet.ANY, ValueSet.just(A)).isAny());
        assertEquals(ValueSet.just(A), met(ValueSet.ANY, ValueSet.just(A)));
    }

    /** Nothing admitted stays nothing under a further rule, and takes an alternative's values. */
    @Test
    void nothingAdmittedIsNotWidenedByAFurtherRule() {
        assertTrue(met(ValueSet.NONE, ValueSet.just(A)).isEmpty());
        assertEquals(ValueSet.just(A), joined(ValueSet.NONE, ValueSet.just(A)));
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
        assertEquals(ValueSet.just(once), met(ValueSet.just(once), ValueSet.just(again)));
        assertTrue(met(ValueSet.just(once), ValueSet.just(Value.number(2))).isEmpty());
    }

    /** And a whole number written as one is the same value as the decimal it equals, so that a
     * position read through either spelling holds one set of values. */
    @Test
    void aWholeNumberIsTheNumberItEquals() {
        assertEquals(Value.number(1), Value.number(new BigDecimal("1.000")));
    }

    /**
     * Runs of whole numbers put together with every shape leave exactly the numbers both, or
     * either, hold — asked number by number over a window that reaches past every end.
     */
    @Test
    void runsOfWholeNumbersMetAndJoinedLeaveWhatBothAndEitherHold() {
        ValueSet low = ValueSet.wholeNumbers(runs(0, 3).or(runs(8, null)));
        ValueSet high = ValueSet.wholeNumbers(runs(null, -2).or(runs(5, 6)));
        List<ValueSet> others = List.of(low, high,
                ValueSet.oneOf(Set.of(Value.number(1), Value.number(3), Value.number(9))),
                new ValueSet.Cofinite(Set.of(Value.number(2), Value.number(8))),
                ValueSet.ANY, ValueSet.NONE);
        for (ValueSet one : List.of(low, high)) {
            assertTrue(one instanceof ValueSet.WholeRuns, () -> "runs are held as runs: " + one);
            for (ValueSet other : others) {
                ValueSet both = met(one, other);
                ValueSet either = joined(one, other);
                for (long n = -12; n <= 12; n++) {
                    Value at = Value.number(n);
                    String said = one + " and " + other + " at " + n;
                    assertEquals(one.has(at) && other.has(at), both.has(at), "both " + said);
                    assertEquals(one.has(at) || other.has(at), either.has(at), "either " + said);
                }
                assertEquals(both, met(other, one), "a meet is the same either way round");
            }
        }
        ValueSet words = ValueSet.matching(Language.ofWords(Set.of("x", "yy"),
                PatternPlan.Budget.OF_WHAT_A_RULE_LEAVES.meter()));
        assertTrue(met(low, words).isEmpty(), "whole numbers are no strings");
        assertFalse(low.sharesAnythingWith(words));
        assertTrue(low.sharesAnythingWith(new ValueSet.Cofinite(Set.of(Value.number(0)))),
                "runs from eight on share with everything but nought");
        assertFalse(ValueSet.wholeNumbers(runs(0, 3).or(runs(10, 12))).sharesAnythingWith(
                new ValueSet.Cofinite(Set.of(Value.number(0), Value.number(1), Value.number(2),
                        Value.number(3), Value.number(10), Value.number(11), Value.number(12)))),
                "what is left out is every number of the runs");
    }

    /** Runs that are numbers apart are those numbers, and runs leaving out numbers apart are
     *  every number but those: one shape each, whichever way they were come to. */
    @Test
    void runsThatTheOtherShapesHoldAreThoseShapes() {
        assertEquals(ValueSet.oneOf(Set.of(Value.number(1), Value.number(4))),
                ValueSet.wholeNumbers(runs(1, 1).or(runs(4, 4))));
        assertEquals(new ValueSet.Cofinite(Set.of(Value.number(2))),
                ValueSet.wholeNumbers(runs(2, 2).others()));
        assertEquals(ValueSet.ANY, ValueSet.wholeNumbers(WholeNumberRuns.EVERY));
        assertEquals(ValueSet.NONE, ValueSet.wholeNumbers(WholeNumberRuns.NONE));
        assertFalse(ValueSet.wholeNumbers(runs(0, 3)).has(Value.number(new BigDecimal("1.5"))),
                "a number between two whole ones is in no run");
    }

    /**
     * A set of whole numbers with neighbours in it is spelled as named values where a rule named
     * them and as runs where comparisons left it, and every question about the set answers the same
     * of both spellings — the one that asks whether two sets are one set included.
     */
    @Test
    void twoSpellingsOfOneSetOfWholeNumbersAnswerAlike() {
        ValueSet named = ValueSet.oneOf(Set.of(Value.number(1), Value.number(2)));
        ValueSet left = ValueSet.wholeNumbers(runs(1, 2));
        ValueSet allBut = new ValueSet.Cofinite(Set.of(Value.number(1), Value.number(2)));
        ValueSet leftOut = ValueSet.wholeNumbers(runs(1, 2).others());
        assertTrue(left instanceof ValueSet.WholeRuns && leftOut instanceof ValueSet.WholeRuns,
                "the comparisons' spelling is runs");
        assertFalse(named.equals(left), "and the spelling is what equals is about");

        assertTrue(named.holdsTheSameValuesAs(left));
        assertTrue(left.holdsTheSameValuesAs(named));
        assertTrue(allBut.holdsTheSameValuesAs(leftOut));
        assertTrue(leftOut.holdsTheSameValuesAs(allBut));
        assertFalse(left.holdsTheSameValuesAs(ValueSet.oneOf(Set.of(Value.number(1),
                Value.number(2), Value.number(3)))));
        assertFalse(left.holdsTheSameValuesAs(allBut));
        assertFalse(left.holdsTheSameValuesAs(ValueSet.oneOf(Set.of(Value.number(1),
                Value.number(2), Value.text("x")))), "a value that is no whole number is in no run");

        for (ValueSet other : List.of(named, left, allBut, leftOut, ValueSet.just(Value.number(1)),
                new ValueSet.Cofinite(Set.of(Value.number(5))))) {
            assertEquals(named.sharesAnythingWith(other), left.sharesAnythingWith(other),
                    () -> "{1, 2} against " + other);
            assertEquals(allBut.sharesAnythingWith(other), leftOut.sharesAnythingWith(other),
                    () -> "all but {1, 2} against " + other);
            assertTrue(met(named, other).holdsTheSameValuesAs(met(left, other)),
                    () -> "{1, 2} met with " + other);
        }
    }

    private static WholeNumberRuns runs(Integer from, Integer to) {
        return WholeNumberRuns.one(from == null ? null : BigInteger.valueOf(from),
                to == null ? null : BigInteger.valueOf(to));
    }
}
