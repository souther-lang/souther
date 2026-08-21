package souther.compiler.numeric;

import souther.compiler.numeric.Towards;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;
import souther.compiler.numeric.NumericDomain.Rel;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A rule is one constraint however it was typed, and what a constraint settles on its own it settles
 * when it is read rather than later.
 *
 * <p>The first half is what a reading keyed on the coefficients could not do: a difference written
 * with coefficients of two fell outside the shape that holds differences, and one of its positions
 * came away with no bound at all while the same rule written with ones bounded it.
 *
 * <p>The second half is what nothing did at all. Over decimals {@code 3 * a} never comes to one, so
 * {@code 3 * a = 1} is a rule no value satisfies — and the interval algebra used to answer it with a
 * range around a third whose two ends are decimals, neither of which is a third.
 */
class TwoWritingsOfOneRuleAreOneConstraintTest {

    private static final String A = "a";
    private static final String B = "b";

    private static Rational num(long whole) {
        return Rational.of(whole);
    }

    private static Rational ratio(long numerator, long denominator) {
        return Rational.of(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator));
    }

    private static Map<String, Rational> weighing(Object... pairs) {
        Map<String, Rational> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], num((Integer) pairs[i + 1]));
        }
        return out;
    }

    private static AffineConstraint<String> whole(Map<String, Rational> coefs, long constant,
                                                  Rel rel) {
        Read<String> read = AffineConstraint.of(coefs, num(constant), rel,
                atom -> Granularity.DISCRETE);
        return assertInstanceOf(Read.Stated.class, read).constraint();
    }

    private static Read<String> decimals(Map<String, Rational> coefs, Rational constant, Rel rel) {
        return AffineConstraint.of(coefs, constant, rel, atom -> Granularity.DENSE);
    }

    // --- one rule, however it was written ---------------------------------------------------------

    /** The rule from the issue: three hundred and six hundred share three hundred, and what they
     *  share goes to the threshold. */
    @Test
    void aScaledRuleIsTheRuleItScales() {
        assertEquals(whole(weighing(A, 1, B, 2), -16, Rel.LE),
                whole(weighing(A, 300, B, 600), -4800, Rel.LE));
    }

    /** The shape that had fallen out: a difference stated with coefficients of two is a difference. */
    @Test
    void aScaledDifferenceIsADifference() {
        assertEquals(whole(weighing(A, 1, B, -1), -2, Rel.LE),
                whole(weighing(A, 2, B, -2), -4, Rel.LE));
    }

    @Test
    void aComparisonWrittenTheOtherWayIsTheSameComparison() {
        assertEquals(whole(weighing(A, 1, B, -1), -2, Rel.LE),
                whole(weighing(B, 1, A, -1), 2, Rel.GE));
        assertEquals(whole(weighing(A, 1), -3, Rel.GE), whole(weighing(A, -1), 3, Rel.LE));
    }

    @Test
    void thePositionsAreNamedInWhateverOrderAndTheRuleIsOne() {
        assertEquals(whole(weighing(A, 1, B, 2), -16, Rel.LE),
                whole(weighing(B, 2, A, 1), -16, Rel.LE));
    }

    @Test
    void aPositionTheRuleDoesNotWeighIsNotOneItNames() {
        Map<String, Rational> withNought = weighing(A, 1, B, 2);
        withNought.put("c", Rational.ZERO);
        assertEquals(whole(weighing(A, 1, B, 2), -16, Rel.LE), whole(withNought, -16, Rel.LE));
    }

    @Test
    void twoRulesThatSayDifferentThingsStayTwo() {
        assertNotEquals(whole(weighing(A, 1), -3, Rel.LE), whole(weighing(A, 1), -3, Rel.LT));
        assertNotEquals(whole(weighing(A, 1), -3, Rel.LE), whole(weighing(A, 1), -4, Rel.LE));
    }

    /**
     * An equality has no direction to turn, so the two ways of writing it have to be made one rule
     * rather than turning into one.
     *
     * <p>A comparison says {@code a >= 3} and {@code -a <= -3} are one thing by reducing both to the
     * same half-space. {@code a = 3} and {@code -a = -3} have no such reduction, and were two
     * records — so the same rule said both ways was two rules in the set.
     */
    @Test
    void anEqualityIsOneRuleWhicheverWayRoundItWasWritten() {
        assertEquals(whole(weighing(A, 1), -3, Rel.EQ), whole(weighing(A, -1), 3, Rel.EQ));
        assertEquals(whole(weighing(A, 1), -3, Rel.EQ).hashCode(),
                whole(weighing(A, -1), 3, Rel.EQ).hashCode());
        assertEquals(whole(weighing(A, 1, B, -1), 0, Rel.EQ),
                whole(weighing(B, 1, A, -1), 0, Rel.EQ));
    }

    @Test
    void aDisequalityIsOneRuleWhicheverWayRoundItWasWritten() {
        assertEquals(whole(weighing(A, 1), -3, Rel.NE), whole(weighing(A, -1), 3, Rel.NE));
        assertEquals(whole(weighing(A, 1), -3, Rel.NE).hashCode(),
                whole(weighing(A, -1), 3, Rel.NE).hashCode());
    }

    @Test
    void anEqualityAtOneValueIsNotAnEqualityAtAnother() {
        assertNotEquals(whole(weighing(A, 1), -3, Rel.EQ), whole(weighing(A, 1), -4, Rel.EQ));
        assertNotEquals(whole(weighing(A, 1), -3, Rel.EQ), whole(weighing(A, 1), -3, Rel.NE));
    }

    // --- what the rule settles on its own ---------------------------------------------------------

    /** Over whole numbers the sum cannot sit between two of its values, so the bound comes down
     *  onto one. Real arithmetic gives one and a half and stops there. */
    @Test
    void aBoundBetweenTwoOfTheSumsValuesComesDownOntoOne() {
        AffineConstraint<String> read = whole(weighing(A, 2, B, 2), -3, Rel.LE);
        assertEquals(new AffineConstraint.HalfSpace<>(
                        new CanonicalForm<>(Map.of(A, Rational.ONE, B, Rational.ONE)),
                        RationalCut.inclusive(num(1))),
                read, "`2x + 2y <= 3` over whole numbers states `x + y <= 1`");
    }

    @Test
    void aStrictBoundOverWholeNumbersLandsOnTheValueBelow() {
        assertEquals(whole(weighing(A, 1), -2, Rel.LE), whole(weighing(A, 1), -3, Rel.LT));
    }

    @Test
    void aBoundBelowZeroComesDownRatherThanTowardsIt() {
        assertEquals(whole(weighing(A, 1), 2, Rel.GE), whole(weighing(A, 2), 5, Rel.GE),
                "`2a >= -5` is `a >= -2` and never `a >= -3`");
        assertNotEquals(whole(weighing(A, 1), 3, Rel.GE), whole(weighing(A, 2), 5, Rel.GE),
                "which is the direction rounding toward zero would get wrong");
    }

    /** The measurement that started this. Two layers of the compiler disagreed about whether
     *  {@code 3 * a} comes to one; it does not, and an equality at one holds of nothing. */
    @Test
    void anEqualityAtAValueTheSumCannotReachHoldsOfNothing() {
        assertInstanceOf(Read.HoldsNever.class,
                decimals(weighing(A, 3), num(-1), Rel.EQ));
        assertInstanceOf(Read.Stated.class, decimals(weighing(A, 3), num(-3), Rel.EQ),
                "and three is a value it does reach");
    }

    /** The same fact on the other side: held away from a value it never takes, it is held away from
     *  nothing. */
    @Test
    void aDisequalityAtSuchAValueHoldsOfEverything() {
        assertInstanceOf(Read.HoldsAlways.class, decimals(weighing(A, 3), num(-1), Rel.NE));
        assertInstanceOf(Read.Stated.class, decimals(weighing(A, 3), num(-3), Rel.NE));
    }

    /** And a bound at such a value is a bound the sum comes arbitrarily close to and never reaches,
     *  which is the strict comparison — the same rule written either way. */
    @Test
    void aBoundAtSuchAValueIsStrict() {
        assertEquals(decimals(weighing(A, 3), num(-1), Rel.LT),
                decimals(weighing(A, 3), num(-1), Rel.LE),
                "`3a <= 1` and `3a < 1` admit the same decimals");
        AffineConstraint<String> read =
                assertInstanceOf(Read.Stated.class, decimals(weighing(A, 3), num(-1), Rel.LE))
                        .constraint();
        assertEquals(new AffineConstraint.HalfSpace<>(
                        new CanonicalForm<>(Map.of(A, Rational.ONE)),
                        RationalCut.exclusive(ratio(1, 3))),
                read);
    }

    @Test
    void aBoundAtAValueTheSumDoesReachKeepsWhateverTheRuleSaid() {
        assertNotEquals(decimals(weighing(A, 3), num(-3), Rel.LT),
                decimals(weighing(A, 3), num(-3), Rel.LE));
    }

    // --- a comparison that names nobody -----------------------------------------------------------

    @Test
    void aComparisonOfConstantsSettlesItself() {
        assertInstanceOf(Read.HoldsAlways.class,
                AffineConstraint.of(Map.of(), num(-1), Rel.LE, atom -> Granularity.DISCRETE));
        assertInstanceOf(Read.HoldsNever.class,
                AffineConstraint.of(Map.of(), num(1), Rel.LE, atom -> Granularity.DISCRETE));
        assertInstanceOf(Read.HoldsAlways.class,
                AffineConstraint.of(Map.of(), Rational.ZERO, Rel.EQ, atom -> Granularity.DISCRETE));
        assertInstanceOf(Read.HoldsNever.class,
                AffineConstraint.of(Map.of(), Rational.ZERO, Rel.NE, atom -> Granularity.DISCRETE));
    }

    // --- a disequality stays a hole ----------------------------------------------------------------

    /**
     * Never turned into a bound here. Which side of the hole the sum lies is not something the rule
     * says — it is something the rest of what is known says, and it can become known long after this
     * arrived. Deciding it on the way in is what made the answer depend on which rule was written
     * first.
     */
    @Test
    void aDisequalityIsHeldAsAHoleAndNotAsABound() {
        assertInstanceOf(AffineConstraint.Disequality.class,
                whole(weighing(A, 1), 0, Rel.NE));
    }
}
