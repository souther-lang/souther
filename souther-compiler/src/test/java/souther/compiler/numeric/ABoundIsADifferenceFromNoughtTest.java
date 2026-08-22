package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;
import souther.compiler.numeric.NumericDomain.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A bound on a position and a bound on a difference are one shape, and closing them over each other
 * answers what each position is left, what each difference is left, and whether anything is left at
 * all — which had been three readings that had to agree.
 */
class ABoundIsADifferenceFromNoughtTest {

    private static final String A = "a";
    private static final String B = "b";
    private static final String C = "c";

    private static Rational num(long whole) {
        return Rational.of(whole);
    }

    private static Rational ratio(long numerator, long denominator) {
        return Rational.of(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator));
    }

    /** A little builder for `Σ c·x + k rel 0`, read the way the algebra reads it. */
    private static final class Rules {

        private final List<AffineConstraint<String>> stated = new ArrayList<>();
        private final Granularity spacing;

        Rules(Granularity spacing) {
            this.spacing = spacing;
        }

        Rules say(Map<String, Rational> coefs, Rational constant, Rel rel) {
            Read<String> read = AffineConstraint.of(coefs, constant, rel, atom -> spacing);
            stated.add(stated(read));
            return this;
        }

        Rules say(Map<String, Rational> coefs, long constant, Rel rel) {
            return say(coefs, num(constant), rel);
        }

        DifferenceBounds<String> closed() {
            return DifferenceBounds.over(stated);
        }
    }

    private static Rules whole() {
        return new Rules(Granularity.DISCRETE);
    }

    private static Map<String, Rational> weighing(Object... pairs) {
        Map<String, Rational> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], num((Integer) pairs[i + 1]));
        }
        return out;
    }

    // --- one shape for both -----------------------------------------------------------------------

    @Test
    void aBoundOnAPositionIsReadBack() {
        DifferenceBounds<String> closed = whole()
                .say(weighing(A, 1), -10, Rel.LE)
                .say(weighing(A, 1), -3, Rel.GE)
                .closed();
        assertEquals(RationalCut.inclusive(num(10)), closed.upperBoundOf(A));
        assertEquals(RationalCut.inclusive(num(3)), closed.lowerBoundOf(A));
        assertFalse(closed.holdsNothing());
    }

    /** The whole point of closing: nothing was ever said about {@code a} alone. */
    @Test
    void aBoundReachesAPositionThroughADifference() {
        DifferenceBounds<String> closed = whole()
                .say(weighing(A, 1, B, -1), 0, Rel.LE)      // a - b <= 0
                .say(weighing(B, 1), -1440, Rel.LE)         // b <= 1440
                .closed();
        assertEquals(RationalCut.inclusive(num(1440)), closed.upperBoundOf(A));
        assertNull(closed.lowerBoundOf(A), "and nothing bounds it below");
    }

    @Test
    void differencesComposeAlongAPath() {
        DifferenceBounds<String> closed = whole()
                .say(weighing(A, 1, B, -1), -2, Rel.LE)     // a - b <= 2
                .say(weighing(B, 1, C, -1), -5, Rel.LE)     // b - c <= 5
                .closed();
        assertEquals(RationalCut.inclusive(num(7)), closed.differenceBound(A, C));
    }

    /** A path reaches its far end only where every hop on it does. */
    @Test
    void oneUnreachedHopMakesTheWholePathUnreached() {
        DifferenceBounds<String> closed = new Rules(Granularity.DENSE)
                .say(weighing(A, 1, B, -1), -2, Rel.LE)     // a - b <= 2
                .say(weighing(B, 1, C, -1), -5, Rel.LT)     // b - c < 5
                .closed();
        assertEquals(RationalCut.exclusive(num(7)), closed.differenceBound(A, C));
    }

    @Test
    void twoRulesOnOneEdgeLeaveTheTighter() {
        DifferenceBounds<String> closed = whole()
                .say(weighing(A, 1), -10, Rel.LE)
                .say(weighing(A, 1), -4, Rel.LE)
                .closed();
        assertEquals(RationalCut.inclusive(num(4)), closed.upperBoundOf(A));
    }

    @Test
    void aPositionIsNoDistanceFromItself() {
        assertEquals(RationalCut.inclusive(Rational.ZERO),
                whole().say(weighing(A, 1), -10, Rel.LE).closed().differenceBound(A, A));
    }

    // --- the shapes canonicalisation brought in ---------------------------------------------------

    /** {@code 2a <= 10} is {@code a <= 5}, and is a bound on a position like any other. Read off the
     *  coefficients as they were typed, it was neither shape and left {@code a} unbounded. */
    @Test
    void aScaledBoundIsABound() {
        assertEquals(RationalCut.inclusive(num(5)),
                whole().say(weighing(A, 2), -10, Rel.LE).closed().upperBoundOf(A));
    }

    /** And {@code 2a - 2b <= 4} is a difference, which is what left {@code a} with nothing at all
     *  while the same rule written with ones bounded it at twelve. */
    @Test
    void aScaledDifferenceIsADifference() {
        DifferenceBounds<String> closed = whole()
                .say(weighing(A, 2, B, -2), -4, Rel.LE)
                .say(weighing(B, 1), -10, Rel.LE)
                .closed();
        assertEquals(RationalCut.inclusive(num(12)), closed.upperBoundOf(A));
    }

    @Test
    void anEqualityIsBothBounds() {
        DifferenceBounds<String> closed = whole().say(weighing(A, 1), -7, Rel.EQ).closed();
        assertEquals(RationalCut.inclusive(num(7)), closed.upperBoundOf(A));
        assertEquals(RationalCut.inclusive(num(7)), closed.lowerBoundOf(A));
    }

    // --- what it does not hold ---------------------------------------------------------------------


    /** The constraint {@code read} states, where it states one. Asked through the reading's own
     *  type, so that what comes back is a constraint over the same positions the reading was of. */
    private static AffineConstraint<String> stated(Read<String> read) {
        assertInstanceOf(Read.Stated.class, read);
        return ((Read.Stated<String>) read).constraint();
    }

    @Test
    void aSumOfTwoPositionsIsNotOfThisShape() {
        AffineConstraint<String> sum = stated(
                AffineConstraint.of(weighing(A, 1, B, 1), num(-10), Rel.LE,
                        atom -> Granularity.DISCRETE));
        assertFalse(DifferenceBounds.canHold(sum));
        assertTrue(DifferenceBounds.over(List.of(sum)).positions().isEmpty(),
                "so it leaves the positions to whatever holds the rest");
    }

    @Test
    void aWeightedDifferenceThatDoesNotReduceIsNotOfThisShape() {
        AffineConstraint<String> skew = stated(
                AffineConstraint.of(weighing(A, 2, B, -3), num(-10), Rel.LE,
                        atom -> Granularity.DISCRETE));
        assertFalse(DifferenceBounds.canHold(skew));
    }

    @Test
    void aHoleIsNotABound() {
        AffineConstraint<String> hole = stated(
                AffineConstraint.of(weighing(A, 1), Rational.ZERO, Rel.NE,
                        atom -> Granularity.DISCRETE));
        assertFalse(DifferenceBounds.canHold(hole));
    }

    // --- and when the rules leave nothing ----------------------------------------------------------

    @Test
    void boundsThatCrossLeaveNothing() {
        assertTrue(whole()
                .say(weighing(A, 1), -10, Rel.GE)
                .say(weighing(A, 1), -3, Rel.LE)
                .closed().holdsNothing());
    }

    @Test
    void aCycleOfDifferencesComingBackLowerLeavesNothing() {
        assertTrue(whole()
                .say(weighing(A, 1, B, -1), 1, Rel.LE)      // a - b <= -1
                .say(weighing(B, 1, A, -1), 1, Rel.LE)      // b - a <= -1
                .closed().holdsNothing());
    }

    /** Nought is a difference a position is from itself, so a cycle that reaches nought without
     *  admitting it leaves nothing either. */
    @Test
    void aCycleReachingNoughtWithoutAdmittingItLeavesNothing() {
        assertTrue(new Rules(Granularity.DENSE)
                .say(weighing(A, 1, B, -1), 0, Rel.LT)      // a - b < 0
                .say(weighing(B, 1, A, -1), 0, Rel.LE)      // b - a <= 0
                .closed().holdsNothing());
    }

    @Test
    void anEmptinessReachedOnlyThroughAPathIsStillFound() {
        assertTrue(whole()
                .say(weighing(A, 1, B, -1), 0, Rel.LE)      // a <= b
                .say(weighing(B, 1, C, -1), 0, Rel.LE)      // b <= c
                .say(weighing(C, 1), -5, Rel.LE)            // c <= 5
                .say(weighing(A, 1), -9, Rel.GE)            // a >= 9
                .closed().holdsNothing());
    }

    /**
     * Exactly, and not to whatever a rounded decimal would have made of it. The two ends of this sit
     * a third apart, which is finer than any fixed number of digits keeps.
     */
    @Test
    void anEmptinessFinerThanRoundingIsStillFound() {
        assertTrue(new Rules(Granularity.DENSE)
                .say(Map.of(A, num(3)), num(-1), Rel.GE)    // 3a >= 1, so a >= 1/3
                .say(Map.of(A, num(3)), ratio(-999_999, 1_000_000), Rel.LE)
                .closed().holdsNothing(),
                "a is at least a third and at most a hair under one, which nothing satisfies");
    }

    /**
     * And where nothing is left, there is no tightest bound to be had.
     *
     * <p>Refused rather than answered. Closing a system that comes back below where it started walks
     * the cycle as often as the closure happened to reach it, so a number handed back here moves
     * with the order the rules arrived in — measured, and it did. Answering "no bound" instead would
     * read as unbounded, which is the opposite of the truth and would send a reader looking for rows
     * in a value nobody can build.
     */
    @Test
    void aClosureThatLeavesNothingHasNoTightestBound() {
        DifferenceBounds<String> nothing = whole()
                .say(weighing(A, 1), -10, Rel.GE)
                .say(weighing(A, 1), -3, Rel.LE)
                .closed();
        assertTrue(nothing.holdsNothing());
        assertThrows(IllegalStateException.class, () -> nothing.upperBoundOf(A));
        assertThrows(IllegalStateException.class, () -> nothing.lowerBoundOf(A));
        assertThrows(IllegalStateException.class, () -> nothing.differenceBound(A, B));
        assertThrows(IllegalStateException.class, () -> nothing.differenceBound(A, A),
                "including the one a position is from itself, which otherwise answers nought");
    }

    @Test
    void nothingContradictoryLeavesSomething() {
        assertFalse(whole()
                .say(weighing(A, 1), -10, Rel.LE)
                .say(weighing(A, 1), -3, Rel.GE)
                .say(weighing(A, 1, B, -1), 0, Rel.LE)
                .closed().holdsNothing());
    }
}
