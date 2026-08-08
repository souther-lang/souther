package souther.compiler.numeric;

import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

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

    /** The same two over whole numbers. {@code 2a <= 5} admits no integer above 2, so that is the
     * bound: a remainder under an integer atom is a value the atom cannot take. */
    @Test
    void aWholeNumberBoundIsSharpenedByItsSpacing() {
        NumericDomain d = NumericDomain.top()
                .assume(times(2, A).minus(num(5)), Rel.LE, whole(A));

        assertTrue(provesAtMost(d, A, 2), "no integer over two satisfies 2a <= 5");
        assertFalse(provesAtMost(d, A, 1), "a = 2 satisfies it");
    }

    @Test
    void aWholeNumberLowerBoundIsSharpenedTheOtherWay() {
        NumericDomain d = NumericDomain.top()
                .assume(times(-2, A).plus(num(5)), Rel.LE, whole(A));

        assertTrue(provesAtLeast(d, A, 3), "no integer under three satisfies a >= 2.5");
        assertFalse(provesAtLeast(d, A, 4), "a = 3 satisfies it");
    }

    // --- strictness on one atom -------------------------------------------------------------------

    /** {@code a < 3} over the reals bounds nothing below 3, and that is the whole of it. */
    @Test
    void aStrictBoundOnADenseAtomGivesNothingTighterThanTheValue() {
        NumericDomain d = NumericDomain.top().assume(atom(A).minus(num(3)), Rel.LT, dense(A));

        assertTrue(provesAtMost(d, A, 3));
        assertFalse(provesAtMost(d, A, 2), "2.5 is under three and over two");
    }

    /** {@code a < 3} over the integers is {@code a <= 2}. */
    @Test
    void aStrictBoundOnAWholeNumberStepsDownToTheNextValue() {
        NumericDomain d = NumericDomain.top().assume(atom(A).minus(num(3)), Rel.LT, whole(A));

        assertTrue(provesAtMost(d, A, 2));
        assertFalse(provesAtMost(d, A, 1), "a = 2 satisfies it");
    }

    /** And {@code a > 3} is {@code a >= 4}. */
    @Test
    void aStrictLowerBoundOnAWholeNumberStepsUp() {
        NumericDomain d = NumericDomain.top().assume(atom(A).minus(num(3)), Rel.GT, whole(A));

        assertTrue(provesAtLeast(d, A, 4));
        assertFalse(provesAtLeast(d, A, 5), "a = 4 satisfies it");
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
        NumericDomain d = NumericDomain.top()
                .assume(atom(A).minus(atom(B)), Rel.LT, whole(A, B))
                .assume(atom(B).minus(num(1440)), Rel.LE, whole(B));

        assertTrue(provesAtMost(d, A, 1439), "a <= b - 1 <= 1439");
        assertFalse(provesAtMost(d, A, 1438), "a = 1439 with b = 1440 satisfies it");
    }

    /** One dense atom on either side and the difference has no smallest step again: {@code a} may be
     * {@code 1439.5} when {@code b} is 1440. */
    @Test
    void aStrictDifferenceWithOneDenseSideTakesNoStep() {
        Map<String, Granularity> mixed = new LinkedHashMap<>(whole(A));
        mixed.putAll(dense(B));
        NumericDomain d = NumericDomain.top()
                .assume(atom(A).minus(atom(B)), Rel.LT, mixed)
                .assume(atom(B).minus(num(1440)), Rel.LE, dense(B));

        assertTrue(provesAtMost(d, A, 1440));
        assertFalse(provesAtMost(d, A, 1439), "nothing here says b is a whole number");
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

    // --- what an assertion arrived with and the domain did not keep --------------------------------

    @Test
    void anIntervalAndADifferenceOverWholeNumbersLoseNothing() {
        NumericDomain d = NumericDomain.top()
                .assume(atom(A).minus(atom(B)), Rel.LT, whole(A, B))
                .assume(atom(B).minus(num(1440)), Rel.LE, whole(B))
                .assume(atom(A).negate(), Rel.LE, whole(A));

        assertTrue(d.projectionIsLossless(), () -> "lost " + d.lossyAtoms());
    }

    /** A loss names the atoms the rule was written about, which is what a reader of it is told. */
    @Test
    void aLossNamesTheAtomsTheRuleWasWrittenAbout() {
        NumericDomain d = NumericDomain.top()
                .assume(atom(A), Rel.NE, whole(A))
                .assume(atom(B).minus(num(10)), Rel.LE, whole(B));

        assertEquals(Set.of(A), d.lossyAtoms());
        assertFalse(d.projectionIsLossless(), "and the domain is not all of what it was told");
    }

    /** A strict bound over decimals is recorded as the non-strict one, so the edge it names is a
     * value the rule refuses. Sound as a bound, and not an edge anybody can write. */
    @Test
    void aStrictBoundOnADenseAtomIsRecordedAsALoss() {
        NumericDomain interval = NumericDomain.top()
                .assume(atom(A).minus(num(3)), Rel.LT, dense(A));
        NumericDomain difference = NumericDomain.top()
                .assume(atom(A).minus(atom(B)), Rel.LT, dense(A, B));

        assertFalse(interval.projectionIsLossless());
        assertEquals(Set.of(NumericDomain.Loss.WEAKENED_STRICT), interval.lossesAt(A));
        assertEquals(Set.of(A, B), difference.lossyAtoms(),
                "a difference is a rule about both of its ends");
    }

    /** The same over whole numbers keeps everything: there the strictness became a step. */
    @Test
    void aStrictBoundOnAWholeNumberIsNoLoss() {
        assertTrue(NumericDomain.top().assume(atom(A).minus(num(3)), Rel.LT, whole(A))
                .projectionIsLossless());
    }

    /** A disequality is a hole in a range, and a range is all this holds. */
    @Test
    void aDisequalityIsRecordedAsALoss() {
        NumericDomain d = NumericDomain.top().assume(atom(A), Rel.NE, whole(A));

        assertEquals(Set.of(NumericDomain.Loss.DROPPED_DISEQUALITY), d.lossesAt(A));
    }

    /** A form of neither shape proves things and no bound is derived through it. */
    @Test
    void aFormOfNeitherShapeIsRecordedAsALoss() {
        NumericDomain d = NumericDomain.top()
                .assume(atom(A).plus(atom(B)).minus(num(10)), Rel.LE, whole(A, B));

        assertEquals(Set.of(A, B), d.lossyAtoms());
        assertEquals(Set.of(NumericDomain.Loss.KEPT_UNPROJECTABLE), d.lossesAt(A));
        assertTrue(d.entails(atom(A).plus(atom(B)).minus(num(10)), Rel.LE),
                "still proves what it was told, and holds no bound from it");
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
