package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A form's values are what its coefficients generate over what its positions hold, and not every
 * number on the order those positions sit on. Over decimals {@code 3 * a} never comes to one, so a
 * bound written at one is a bound at a value nothing stands on — which decides three separate
 * questions: whether an equality can hold, whether a cut can move, and whether a cut is strict.
 */
class WhatAFormAddsUpToIsNotWhatItsOrderHoldsTest {

    private static Rational ratio(long numerator, long denominator) {
        return Rational.of(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator));
    }

    private static Map<String, Rational> form(Object... pairs) {
        Map<String, Rational> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], Rational.of((long) (int) (Integer) pairs[i + 1]));
        }
        return out;
    }

    private static AdditiveImage over(Map<String, Rational> coefs, Granularity everywhere) {
        return AdditiveImage.of(coefs, atom -> everywhere);
    }

    // --- over positions that step ---------------------------------------------------------------

    @Test
    void aFormOverWholeNumbersTakesTheMultiplesOfItsDivisor() {
        AdditiveImage image = over(form("s", 300, "c", 600), Granularity.DISCRETE);
        assertEquals(Rational.of(300), image.generator());
        assertTrue(image.isExact());
        assertTrue(image.contains(Rational.of(4800)));
        assertTrue(image.contains(Rational.of(-900)));
        assertFalse(image.contains(Rational.of(4900)));
    }

    @Test
    void coprimeCoefficientsReachEveryWholeNumber() {
        AdditiveImage image = over(form("a", 2, "b", 3), Granularity.DISCRETE);
        assertEquals(Rational.ONE, image.generator());
        assertTrue(image.contains(Rational.of(1)), "two and three make one, which is Bezout's");
    }

    /** The rule {@code NumericDomain} already applies to one position, one level up: a bound
     *  between two values the form takes moves down onto the one below. */
    @Test
    void anUpperCutMovesOntoTheValueBelowIt() {
        AdditiveImage image = over(form("a", 1), Granularity.DISCRETE);
        assertEquals(RationalCut.inclusive(Rational.of(3)),
                image.tightenUpper(RationalCut.inclusive(ratio(7, 2))));
        assertEquals(RationalCut.inclusive(Rational.of(2)),
                image.tightenUpper(RationalCut.exclusive(Rational.of(3))),
                "`a < 3` over whole numbers is `a <= 2`");
        assertEquals(RationalCut.inclusive(Rational.of(3)),
                image.tightenUpper(RationalCut.inclusive(Rational.of(3))),
                "and a bound already on a value it takes does not move");
    }

    @Test
    void aLowerCutMovesOntoTheValueAboveIt() {
        AdditiveImage image = over(form("a", 1), Granularity.DISCRETE);
        assertEquals(RationalCut.inclusive(Rational.of(4)),
                image.tightenLower(RationalCut.inclusive(ratio(7, 2))));
        assertEquals(RationalCut.inclusive(Rational.of(4)),
                image.tightenLower(RationalCut.exclusive(Rational.of(3))));
        assertEquals(RationalCut.inclusive(Rational.of(-3)),
                image.tightenLower(RationalCut.inclusive(ratio(-7, 2))),
                "and the same below zero, where rounding toward zero would go the wrong way");
    }

    /** What the user's example turns on: over whole numbers {@code 2x + 2y <= 3} states
     *  {@code x + y <= 1}, which is not something real arithmetic gives. */
    @Test
    void aCutBetweenTheFormsValuesIsTightenedOntoOne() {
        AdditiveImage image = over(form("x", 2, "y", 2), Granularity.DISCRETE);
        assertEquals(Rational.of(2), image.generator());
        assertEquals(RationalCut.inclusive(Rational.of(2)),
                image.tightenUpper(RationalCut.inclusive(Rational.of(3))),
                "`2x + 2y <= 3` is `2x + 2y <= 2`, which is `x + y <= 1`");
    }

    @Test
    void aDivisorTheCoefficientsShareCanBeADecimal() {
        Map<String, Rational> halves = new LinkedHashMap<>();
        halves.put("a", ratio(1, 2));
        halves.put("b", ratio(1, 4));
        AdditiveImage image = AdditiveImage.of(halves, atom -> Granularity.DISCRETE);
        assertEquals(ratio(1, 4), image.generator());
        assertTrue(image.contains(ratio(3, 4)));
        assertFalse(image.contains(ratio(1, 8)));
    }

    // --- over positions whose values fill --------------------------------------------------------

    /** The measurement that started this: two layers of the compiler disagreed about whether
     *  {@code 3 * a} comes to one. It does not. */
    @Test
    void aFormOverDecimalsDoesNotReachWhatItsDivisorDoesNotDivide() {
        AdditiveImage image = over(form("a", 3), Granularity.DENSE);
        assertEquals(Rational.of(3), image.generator());
        assertTrue(image.isExact());
        assertFalse(image.contains(Rational.of(1)), "a third is not a decimal anybody writes");
        assertTrue(image.contains(Rational.of(3)));
        assertTrue(image.contains(ratio(3, 10)), "and it is still dense: a tenth of three is one");
    }

    @Test
    void tenIsAUnitSoTwoAndFiveAre() {
        assertEquals(Rational.ONE, over(form("a", 2), Granularity.DENSE).generator());
        assertEquals(Rational.ONE, over(form("a", 5), Granularity.DENSE).generator());
        assertEquals(Rational.ONE, over(form("a", 10), Granularity.DENSE).generator());
        assertEquals(Rational.of(3), over(form("a", 6), Granularity.DENSE).generator(),
                "six is a two and a three, and only the three is left");
        assertTrue(over(form("a", 2), Granularity.DENSE).contains(ratio(1, 100)));
    }

    /** No greatest value below an unreached one, so the cut cannot move — what it can say is that
     *  the value is out, which is why {@code 3a <= 1} and {@code 3a < 1} are one rule. */
    @Test
    void anUnreachedUpperCutBecomesStrictWhereItStands() {
        AdditiveImage image = over(form("a", 3), Granularity.DENSE);
        assertEquals(RationalCut.exclusive(Rational.of(1)),
                image.tightenUpper(RationalCut.inclusive(Rational.of(1))));
        assertEquals(RationalCut.exclusive(Rational.of(1)),
                image.tightenUpper(RationalCut.exclusive(Rational.of(1))));
        assertEquals(RationalCut.inclusive(Rational.of(3)),
                image.tightenUpper(RationalCut.inclusive(Rational.of(3))),
                "and a cut at a value it does reach keeps the value");
        assertEquals(RationalCut.exclusive(Rational.of(3)),
                image.tightenUpper(RationalCut.exclusive(Rational.of(3))),
                "including when the rule was written to exclude it");
    }

    // --- positions that are not all of one kind --------------------------------------------------

    /**
     * The case the partition layer never faces, because a border's quantity is over one carrier.
     * Nothing stops a guard relating an {@code Int} to a {@code Decimal}, and the true image is
     * neither of the two shapes — so it answers with a set holding it and says so.
     */
    @Test
    void aFormOverBothAnswersWiderAndSaysSo() {
        Map<String, Granularity> kinds = new LinkedHashMap<>();
        kinds.put("x", Granularity.DISCRETE);
        kinds.put("y", Granularity.DENSE);
        AdditiveImage image = AdditiveImage.of(form("x", 1, "y", 3), kinds::get);
        assertFalse(image.isExact(), "`x + 3y` reaches no tenth, though its divisor is one");
        assertTrue(image.contains(ratio(1, 10)), "so this is the wider answer, which is the safe one");
        assertFalse(over(form("x", 1, "y", 3), Granularity.DISCRETE).contains(ratio(1, 10)),
                "where the exact answer over whole numbers refuses it");
    }

    // --- what it refuses to be asked --------------------------------------------------------------

    @Test
    void aFormNamingNoPositionIsNotAskedAboutHere() {
        assertThrows(IllegalArgumentException.class,
                () -> AdditiveImage.of(Map.<String, Rational>of(), atom -> Granularity.DISCRETE));
    }

    @Test
    void aSpacingIsNeverGuessed() {
        assertThrows(IllegalStateException.class,
                () -> AdditiveImage.of(form("a", 1), atom -> null));
    }

    @Test
    void aZeroCoefficientIsAPositionTheFormDoesNotName() {
        Map<String, Rational> withZero = new LinkedHashMap<>();
        withZero.put("a", Rational.ZERO);
        assertThrows(IllegalArgumentException.class,
                () -> AdditiveImage.of(withZero, atom -> Granularity.DISCRETE));
    }
}
