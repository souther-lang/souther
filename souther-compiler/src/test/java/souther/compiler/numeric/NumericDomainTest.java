package souther.compiler.numeric;

import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

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

    private static LinearForm atom(String a) {
        return LinearForm.atom(a);
    }

    private static LinearForm num(long n) {
        return LinearForm.constant(BigDecimal.valueOf(n));
    }

    /** {@code coefficient · atom}, which is how a bound with a divisor is written. */
    private static LinearForm times(long coefficient, String a) {
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
    private static boolean provesAtMost(NumericDomain d, String a, long n) {
        return d.entails(atom(a).minus(num(n)), Rel.LE);
    }

    /** Whether the domain proves {@code a >= n}. */
    private static boolean provesAtLeast(NumericDomain d, String a, long n) {
        return d.entails(atom(a).minus(num(n)), Rel.GE);
    }

    // --- one atom, a divisor, and the direction the rounding has to go ----------------------------

    /** {@code 2a <= 5} is {@code a <= 2.5}. Rounded the wrong way it would be {@code a <= 2}, which
     * refuses {@code a = 2.5} — a value the constraint admits. */
    @Test
    void anUpperBoundWithARemainderIsNeverRoundedDown() {
        NumericDomain d = NumericDomain.top()
                .assume(times(2, A).minus(num(5)), Rel.LE, dense(A));

        assertTrue(provesAtMost(d, A, 3), "2a <= 5 gives a <= 2.5, so a <= 3 follows");
        assertFalse(provesAtMost(d, A, 2), "a = 2.5 satisfies it, so a <= 2 does not follow");
    }

    /** The mirror: {@code -2a <= -5} is {@code a >= 2.5}, and rounding up would refuse 2.5. */
    @Test
    void aLowerBoundWithARemainderIsNeverRoundedUp() {
        NumericDomain d = NumericDomain.top()
                .assume(times(-2, A).plus(num(5)), Rel.LE, dense(A));

        assertTrue(provesAtLeast(d, A, 2), "-2a + 5 <= 0 gives a >= 2.5, so a >= 2 follows");
        assertFalse(provesAtLeast(d, A, 3), "a = 2.5 satisfies it, so a >= 3 does not follow");
    }

    /**
     * The same two over whole numbers, as they are answered today.
     *
     * <p>{@code 2a <= 5} over the integers is {@code a <= 2}, and this does not say so: the quotient
     * is rounded away from the constraint without asking what the atom is made of. Blunt rather than
     * wrong — a bound weaker than the true one proves less and refuses nothing — and it is what
     * knowing the spacing is there to sharpen.
     */
    @Test
    void aWholeNumberBoundIsNotYetSharpenedByItsSpacing() {
        NumericDomain d = NumericDomain.top()
                .assume(times(2, A).minus(num(5)), Rel.LE, whole(A));

        assertTrue(provesAtMost(d, A, 3));
        assertFalse(provesAtMost(d, A, 2), "true of every integer satisfying it, and not derived");
    }

    // --- strictness on one atom -------------------------------------------------------------------

    /** {@code a < 3} over the reals bounds nothing below 3, and that is the whole of it. */
    @Test
    void aStrictBoundOnADenseAtomGivesNothingTighterThanTheValue() {
        NumericDomain d = NumericDomain.top().assume(atom(A).minus(num(3)), Rel.LT, dense(A));

        assertTrue(provesAtMost(d, A, 3));
        assertFalse(provesAtMost(d, A, 2), "2.5 is under three and over two");
    }

    /** {@code a < 3} over the integers is {@code a <= 2}. Today it is recorded as {@code a <= 3}. */
    @Test
    void aStrictBoundOnAWholeNumberIsNotYetSteppedDown() {
        NumericDomain d = NumericDomain.top().assume(atom(A).minus(num(3)), Rel.LT, whole(A));

        assertTrue(provesAtMost(d, A, 3));
        assertFalse(provesAtMost(d, A, 2), "true of every integer under three, and not derived");
    }

    // --- strictness on a difference, which is the part a record's invariant writes -----------------

    /** {@code a < b} with {@code b <= 1440} bounds {@code a} at 1440 and no lower, whatever the
     * spacing, while the difference is recorded without its strictness. */
    @Test
    void aStrictDifferenceCarriesNoStepToday() {
        NumericDomain d = NumericDomain.top()
                .assume(atom(A).minus(atom(B)), Rel.LT, whole(A, B))
                .assume(atom(B).minus(num(1440)), Rel.LE, whole(B));

        assertTrue(provesAtMost(d, A, 1440), "through the difference, a <= b <= 1440");
        assertFalse(provesAtMost(d, A, 1439),
                "true of every pair of integers with a < b <= 1440, and not derived");
    }

    /** The same shape over decimals, where 1439 is not derivable and must not become so: {@code a =
     * 1439.5} satisfies {@code a < b <= 1440}. */
    @Test
    void aStrictDifferenceOverDecimalsHasNoStepToTake() {
        NumericDomain d = NumericDomain.top()
                .assume(atom(A).minus(atom(B)), Rel.LT, dense(A, B))
                .assume(atom(B).minus(num(1440)), Rel.LE, dense(B));

        assertTrue(provesAtMost(d, A, 1440));
        assertFalse(provesAtMost(d, A, 1439), "1439.5 satisfies it");
    }

    /** A non-strict relation between two atoms of one domain narrows neither of them. This is what
     * every relational invariant in {@code souther-examples} is, and why they move nothing. */
    @Test
    void aNonStrictDifferenceBetweenEqualDomainsNarrowsNothing() {
        NumericDomain d = NumericDomain.top()
                .assume(atom(A).minus(atom(B)), Rel.LE, whole(A, B))
                .assume(atom(B).minus(num(1440)), Rel.LE, whole(B))
                .assume(atom(A).negate(), Rel.LE, whole(A));

        assertTrue(provesAtMost(d, A, 1440));
        assertFalse(provesAtMost(d, A, 1439), "a = b = 1440 satisfies every one of these");
    }

    // --- what the differences are closed over -----------------------------------------------------

    @Test
    void aBoundReachesAnAtomThroughAChainOfDifferences() {
        NumericDomain d = NumericDomain.top()
                .assume(atom(A).minus(atom(B)), Rel.LE, whole(A, B))
                .assume(atom(B).minus(atom("c")), Rel.LE, whole(B, "c"))
                .assume(atom("c").minus(num(10)), Rel.LE, whole("c"));

        assertTrue(provesAtMost(d, A, 10), "a <= b <= c <= 10");
    }

    @Test
    void contradictingBoundsMakeThePathInfeasible() {
        NumericDomain d = NumericDomain.top()
                .assume(atom(A).minus(num(1)), Rel.GE, whole(A))
                .assume(atom(A), Rel.LE, whole(A));

        assertTrue(d.isBottom(), "a >= 1 and a <= 0 cannot both hold");
    }

    // --- what the domain refuses to be told -------------------------------------------------------

    /** The key is what says two readings are of one value. Two spacings under one key means the
     * naming and the typing disagree, and the answer is to stop rather than to take the safer one. */
    @Test
    void oneAtomIsOneKindOfNumber() {
        NumericDomain d = NumericDomain.top().assume(atom(A).minus(num(3)), Rel.LE, whole(A));

        IllegalStateException thrown = assertThrows(IllegalStateException.class,
                () -> d.assume(atom(A).minus(num(1)), Rel.GE, dense(A)));
        assertTrue(thrown.getMessage().contains(A), thrown.getMessage());
    }

    /** An atom arriving with no spacing is not defaulted. A guess here is a strict bound either
     * wrongly sharpened or silently left blunt, and neither shows up near where the guess was made. */
    @Test
    void anAtomWithNoSpacingIsRefusedRatherThanAssumed() {
        assertThrows(IllegalStateException.class,
                () -> NumericDomain.top().assume(atom(A).minus(num(3)), Rel.LE, Map.of()));
    }

    /** A form over no atoms needs none: {@code 1 <= 0} is decided by arithmetic. */
    @Test
    void aConstantFormNeedsNoSpacingAtAll() {
        assertTrue(NumericDomain.top().assume(num(1), Rel.LE, Map.of()).isBottom());
        assertFalse(NumericDomain.top().assume(num(-1), Rel.LE, Map.of()).isBottom());
    }

    @Test
    void anAssignmentTakesTheSpacingOfWhatIsAssigned() {
        NumericDomain d = NumericDomain.top()
                .assume(atom(A).minus(num(3)), Rel.LE, whole(A))
                .assign(B, atom(A), whole(A, B));

        assertTrue(provesAtMost(d, B, 3), "b was given a, whose bound it takes");
        assertEquals(false, d.isBottom());
    }
}
