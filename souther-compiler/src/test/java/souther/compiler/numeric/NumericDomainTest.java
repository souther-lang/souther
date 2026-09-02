package souther.compiler.numeric;


import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The reasoner on its own, asked in its own terms.
 *
 * <p>Everything else that reads this domain reads it through the invariant-discharge check, which is
 * fail-open: an answer it never got and an answer of "nothing to report" arrive the same way. So the
 * arithmetic has to be held to here or nowhere. What is pinned is both directions — a bound this
 * records must never be tighter than the true one, or a correct program is rejected; and how tight it
 * actually is, because that is what a change to the rounding moves and a test that only checked
 * soundness would let it move silently.
 */
class NumericDomainTest {

    private static final String A = "a";
    private static final String B = "b";

    private static LinearForm<String> atom(String a) {
        return LinearForm.<String>atom(a);
    }

    private static LinearForm<String> num(long n) {
        return LinearForm.<String>constant(BigDecimal.valueOf(n));
    }

    /** {@code coefficient · atom}, which is how a bound with a divisor is written. */
    private static LinearForm<String> times(long coefficient, String a) {
        return atom(a).times(BigDecimal.valueOf(coefficient));
    }

    private static Map<String, Granularity> spaced(Granularity g, String... atoms) {
        Map<String, Granularity> out = new LinkedHashMap<>();
        for (String each : atoms) {
            out.put(each, g);
        }
        return out;
    }

    private static Map<String, Granularity> whole(String... atoms) {
        return spaced(Granularity.DISCRETE, atoms);
    }

    private static Map<String, Granularity> dense(String... atoms) {
        return spaced(Granularity.DENSE, atoms);
    }

    /** Whether the domain proves {@code a <= n}. */
    private static boolean provesAtMost(NumericDomain<String> d, String a, long n) {
        return d.entails(atom(a).minus(num(n)), Rel.LE);
    }

    /** Whether the domain proves {@code a >= n}. */
    private static boolean provesAtLeast(NumericDomain<String> d, String a, long n) {
        return d.entails(atom(a).minus(num(n)), Rel.GE);
    }

    // --- one atom, a divisor, and the direction the rounding has to go ----------------------------

    /** {@code 2a <= 5} is {@code a <= 2.5}. Rounded the wrong way it would be {@code a <= 2}, which
     * refuses {@code a = 2.5} — a value the constraint admits. */
    @Test
    void anUpperBoundWithARemainderIsNeverRoundedDown() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(times(2, A).minus(num(5)), Rel.LE, dense(A));

        assertTrue(provesAtMost(d, A, 3), "2a <= 5 gives a <= 2.5, so a <= 3 follows");
        assertFalse(provesAtMost(d, A, 2), "a = 2.5 satisfies it, so a <= 2 does not follow");
    }

    /** The mirror: {@code -2a <= -5} is {@code a >= 2.5}, and rounding up would refuse 2.5. */
    @Test
    void aLowerBoundWithARemainderIsNeverRoundedUp() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(times(-2, A).plus(num(5)), Rel.LE, dense(A));

        assertTrue(provesAtLeast(d, A, 2), "-2a + 5 <= 0 gives a >= 2.5, so a >= 2 follows");
        assertFalse(provesAtLeast(d, A, 3), "a = 2.5 satisfies it, so a >= 3 does not follow");
    }

    /** The same two over whole numbers. {@code 2a <= 5} admits no integer above 2, so that is the
     * bound: a remainder under an integer atom is a value the atom cannot take. */
    @Test
    void aWholeNumberBoundIsSharpenedByItsSpacing() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(times(2, A).minus(num(5)), Rel.LE, whole(A));

        assertTrue(provesAtMost(d, A, 2), "no integer over two satisfies 2a <= 5");
        assertFalse(provesAtMost(d, A, 1), "a = 2 satisfies it");
    }

    @Test
    void aWholeNumberLowerBoundIsSharpenedTheOtherWay() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(times(-2, A).plus(num(5)), Rel.LE, whole(A));

        assertTrue(provesAtLeast(d, A, 3), "no integer under three satisfies a >= 2.5");
        assertFalse(provesAtLeast(d, A, 4), "a = 3 satisfies it");
    }

    // --- strictness on one atom -------------------------------------------------------------------

    /** {@code a < 3} over the reals bounds nothing below 3, and that is the whole of it. */
    @Test
    void aStrictBoundOnADenseAtomGivesNothingTighterThanTheValue() {
        NumericDomain<String> d = NumericDomain.<String>top().assume(atom(A).minus(num(3)), Rel.LT, dense(A));

        assertTrue(provesAtMost(d, A, 3));
        assertFalse(provesAtMost(d, A, 2), "2.5 is under three and over two");
    }

    /** {@code a < 3} over the integers is {@code a <= 2}. */
    @Test
    void aStrictBoundOnAWholeNumberStepsDownToTheNextValue() {
        NumericDomain<String> d = NumericDomain.<String>top().assume(atom(A).minus(num(3)), Rel.LT, whole(A));

        assertTrue(provesAtMost(d, A, 2));
        assertFalse(provesAtMost(d, A, 1), "a = 2 satisfies it");
    }

    /** And {@code a > 3} is {@code a >= 4}. */
    @Test
    void aStrictLowerBoundOnAWholeNumberStepsUp() {
        NumericDomain<String> d = NumericDomain.<String>top().assume(atom(A).minus(num(3)), Rel.GT, whole(A));

        assertTrue(provesAtLeast(d, A, 4));
        assertFalse(provesAtLeast(d, A, 5), "a = 4 satisfies it");
    }

    /**
     * {@code a > 0} over a dense atom stops at zero without admitting it.
     *
     * <p>The value is where the rule stops and is not one of the values it leaves. Reading the number
     * alone cannot tell that from {@code a >= 0}, and a caller turning a bound into a value somebody
     * has to write needs the difference: zero is what the rule refuses.
     */
    @Test
    void aStrictLowerBoundOnADenseAtomKeepsTheValueOutOfItsOwnRange() {
        NumericDomain<String> d = NumericDomain.<String>top().assume(atom(A), Rel.GT, dense(A));

        assertEquals(Endpoint.exclusive(Count.of(BigDecimal.ZERO)), d.boundsOf(A).min());
    }

    // --- strictness on a difference, which is the part a record's invariant writes -----------------

    /**
     * {@code a < b} with {@code b <= 1440} bounds {@code a} at 1439 over whole numbers.
     *
     * <p>This is the shape a record's invariant writes — the two ends of an interval, each bounded by
     * its own type and related to the other — and 1439 rather than 1440 is the whole of what issue
     * #427 is about: 1440 is a value nothing can be constructed at.
     */
    @Test
    void aStrictDifferenceBetweenWholeNumbersStepsTheBoundThrough() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(atom(B)), Rel.LT, whole(A, B))
                .assume(atom(B).minus(num(1440)), Rel.LE, whole(B));

        assertTrue(provesAtMost(d, A, 1439), "a <= b - 1 <= 1439");
        assertFalse(provesAtMost(d, A, 1438), "a = 1439 with b = 1440 satisfies it");
    }

    /**
     * A dense {@code b} leaves the difference with no smallest step, and {@code a} is still a whole
     * number, so its own bound steps through.
     *
     * <p>Two questions that had been answered as one. The difference {@code a - b} takes no step —
     * nothing here says {@code b} is whole — so the relation cannot be sharpened as a relation. What
     * can be sharpened is {@code a}: put {@code b} at the most it can be and {@code a} is under
     * 1440, and the largest whole number under 1440 is 1439. Which of the two is being tightened is
     * the whole of it, and asking the difference's spacing about a bound on a position answers the
     * wrong question — conservatively, but wrongly: {@code a} could never be 1439.5.
     */
    @Test
    void aWholePositionStepsThroughEvenWhereTheDifferenceCannot() {
        Map<String, Granularity> mixed = new LinkedHashMap<>(whole(A));
        mixed.putAll(dense(B));
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(atom(B)), Rel.LT, mixed)
                .assume(atom(B).minus(num(1440)), Rel.LE, dense(B));

        assertTrue(provesAtMost(d, A, 1439), "a is whole and under 1440");
        assertFalse(provesAtMost(d, A, 1438), "and 1439 is a value it takes, with b just above it");
    }

    /** The same shape over decimals, where 1439 is not derivable and must not become so: {@code a =
     * 1439.5} satisfies {@code a < b <= 1440}. */
    @Test
    void aStrictDifferenceOverDecimalsHasNoStepToTake() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(atom(B)), Rel.LT, dense(A, B))
                .assume(atom(B).minus(num(1440)), Rel.LE, dense(B));

        assertTrue(provesAtMost(d, A, 1440));
        assertFalse(provesAtMost(d, A, 1439), "1439.5 satisfies it");
    }

    /** A non-strict relation between two atoms of one domain narrows neither of them. This is what
     * every relational invariant in {@code souther-examples} is, and why they move nothing. */
    @Test
    void aNonStrictDifferenceBetweenEqualDomainsNarrowsNothing() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(atom(B)), Rel.LE, whole(A, B))
                .assume(atom(B).minus(num(1440)), Rel.LE, whole(B))
                .assume(atom(A).negate(), Rel.LE, whole(A));

        assertTrue(provesAtMost(d, A, 1440));
        assertFalse(provesAtMost(d, A, 1439), "a = b = 1440 satisfies every one of these");
    }

    // --- what the differences are closed over -----------------------------------------------------

    @Test
    void aBoundReachesAnAtomThroughAChainOfDifferences() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(atom(B)), Rel.LE, whole(A, B))
                .assume(atom(B).minus(atom("c")), Rel.LE, whole(B, "c"))
                .assume(atom("c").minus(num(10)), Rel.LE, whole("c"));

        assertTrue(provesAtMost(d, A, 10), "a <= b <= c <= 10");
    }

    @Test
    void contradictingBoundsMakeThePathInfeasible() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(num(1)), Rel.GE, whole(A))
                .assume(atom(A), Rel.LE, whole(A));

        assertTrue(d.isBottom(), "a >= 1 and a <= 0 cannot both hold");
    }

    // --- how much of a rule the ranges handed over are able to state -------------------------------

    /** An interval and a difference are both things a range and its differences state in full. */
    @Test
    void anIntervalAndADifferenceAreStatedByWhatIsHandedOver() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(atom(B)), Rel.LT, whole(A, B))
                .assume(atom(B).minus(num(1440)), Rel.LE, whole(B))
                .assume(atom(A).negate(), Rel.LE, whole(A));

        assertTrue(d.provenByTheBoxAndItsDifferences(atom(A).minus(atom(B)), Rel.LT));
        assertTrue(d.provenByTheBoxAndItsDifferences(atom(B).minus(num(1440)), Rel.LE));
    }

    /** A strict bound over decimals is an end the range stops at without reaching, which is the
     * whole of what was asserted. */
    @Test
    void aStrictBoundOnADenseAtomIsKeptAsAnEndTheRangeDoesNotReach() {
        NumericDomain<String> interval = NumericDomain.<String>top()
                .assume(atom(A).minus(num(3)), Rel.LT, dense(A));

        assertEquals(Endpoint.exclusive(Count.of(3)), interval.boundsOf(A).max());
        assertTrue(interval.provenByTheBoxAndItsDifferences(atom(A).minus(num(3)), Rel.LT));
    }

    /** The same over whole numbers states it too: there the strictness became a step, and the value
     * it steps onto is one the rule admits. */
    @Test
    void aStrictBoundOnAWholeNumberIsStatedByTheStepItTook() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(num(3)), Rel.LT, whole(A));

        assertEquals(Endpoint.inclusive(Count.of(2)), d.boundsOf(A).max());
        assertTrue(d.provenByTheBoxAndItsDifferences(atom(A).minus(num(3)), Rel.LT));
    }

    /**
     * A hole with nothing to side it is the one a range genuinely cannot keep.
     *
     * <p>And a hole at an edge is not: it moves the edge, and the range then says the whole of it.
     * Which of the two a disequality is depends on what else is known, so it is asked of what the
     * rules were found to leave rather than recorded when the rule was read.
     */
    @Test
    void aHoleIsStatedByTheRangesOnlyWhereItMovedAnEdge() {
        NumericDomain<String> loose = NumericDomain.<String>top()
                .assume(atom(A), Rel.NE, whole(A));
        assertFalse(loose.provenByTheBoxAndItsDifferences(atom(A), Rel.NE),
                "nothing says which side of nought a is on, so the range keeps the nought");

        NumericDomain<String> sided = loose.assume(atom(A), Rel.GE, whole(A));
        assertEquals(Endpoint.inclusive(Count.of(1)), sided.boundsOf(A).min());
        assertTrue(sided.provenByTheBoxAndItsDifferences(atom(A), Rel.NE),
                "and here the range states it, because the hole moved the edge onto one");
    }

    /**
     * A rule over two positions narrows both and is still not something two ranges state — the
     * ranges hold every pair of their own values and the rule refuses some of them.
     */
    @Test
    void aRuleOverTwoPositionsNarrowsBothAndIsStillNotARange() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).negate(), Rel.LE, whole(A, B))
                .assume(atom(B).negate(), Rel.LE, whole(A, B))
                .assume(atom(A).plus(atom(B)).minus(num(10)), Rel.LE, whole(A, B));

        assertEquals(Endpoint.inclusive(Count.of(10)), d.boundsOf(A).max());
        assertTrue(d.entails(atom(A).plus(atom(B)).minus(num(10)), Rel.LE),
                "the rules prove it, since one of them is it");
        assertFalse(d.provenByTheBoxAndItsDifferences(atom(A).plus(atom(B)).minus(num(10)), Rel.LE),
                "and the two ranges do not, since they hold a = 10 beside b = 10");
    }

    /** Where the ranges are tight enough to hold it, they state it, and nothing is owed. */
    @Test
    void aRuleOverTwoPositionsIsStatedWhereTheRangesAlreadyHoldIt() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).negate(), Rel.LE, whole(A, B))
                .assume(atom(B).negate(), Rel.LE, whole(A, B))
                .assume(atom(A).minus(num(3)), Rel.LE, whole(A, B))
                .assume(atom(B).minus(num(3)), Rel.LE, whole(A, B))
                .assume(atom(A).plus(atom(B)).minus(num(10)), Rel.LE, whole(A, B));

        assertTrue(d.provenByTheBoxAndItsDifferences(atom(A).plus(atom(B)).minus(num(10)), Rel.LE),
                "a and b are each at most three, so their sum is at most six whatever is picked");
    }

    // --- and whether the ends are numbers anybody can write -----------------------------------------

    @Test
    void endsOnWholeNumbersAreWrittenExactly() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).minus(num(3)), Rel.LE, whole(A));
        assertTrue(d.endsAreWrittenExactly(A));
    }

    /** A third is not a decimal, so the number standing for that edge is a hair outside it. */
    @Test
    void anEndAtAValueNoDecimalWritesIsRoundedPast() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom(A).times(java.math.BigDecimal.valueOf(3)).minus(num(1)),
                        Rel.LE, dense(A));
        assertFalse(d.endsAreWrittenExactly(A));
        assertTrue(d.boundsOf(A).max().at() instanceof Count at
                        && at.at().compareTo(new java.math.BigDecimal("0.3333")) > 0,
                "and it is rounded the way that widens: " + d.boundsOf(A).max());
    }

    // --- what the domain refuses to be told -------------------------------------------------------

    /** The key is what says two readings are of one value. Two spacings under one key means the
     * naming and the typing disagree, and the answer is to stop rather than to take the safer one. */
    @Test
    void oneAtomIsOneKindOfNumber() {
        NumericDomain<String> d = NumericDomain.<String>top().assume(atom(A).minus(num(3)), Rel.LE, whole(A));

        IllegalStateException thrown = assertThrows(IllegalStateException.class,
                () -> d.assume(atom(A).minus(num(1)), Rel.GE, dense(A)));
        assertTrue(thrown.getMessage().contains(A), thrown.getMessage());
    }

    /** An atom arriving with no spacing is not defaulted. A guess here is a strict bound either
     * wrongly sharpened or silently left blunt, and neither shows up near where the guess was made. */
    @Test
    void anAtomWithNoSpacingIsRefusedRatherThanAssumed() {
        assertThrows(IllegalStateException.class,
                () -> NumericDomain.<String>top().assume(atom(A).minus(num(3)), Rel.LE, Map.of()));
    }

    /** A form over no atoms needs none: {@code 1 <= 0} is decided by arithmetic. */
    @Test
    void aConstantFormNeedsNoSpacingAtAll() {
        assertTrue(NumericDomain.<String>top().assume(num(1), Rel.LE, Map.of()).isBottom());
        assertFalse(NumericDomain.<String>top().assume(num(-1), Rel.LE, Map.of()).isBottom());
    }
}
