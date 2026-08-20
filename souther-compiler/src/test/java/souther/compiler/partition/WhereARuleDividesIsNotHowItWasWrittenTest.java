package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Where a rule divides a quantity's values, as against the number it was written with.
 *
 * <p>{@code n <= 4} and {@code n < 5} are two comparisons and one division of the whole numbers:
 * everything up to four on one side, everything from five on the other. Keyed on the threshold they
 * are two lines, and a position carrying both is reported as having three classes, the middle one
 * holding no value any row could write. Keyed on where the values part, they are one.
 *
 * <p>Which is a question about the order and not about the spelling, so the same two operators over
 * a carrier whose values fill answer the other way: no decimal lies between {@code <= 0.5} and
 * {@code < 0.5}, and the two rules put {@code 0.5} itself on opposite sides. A seam that made those
 * one would take a class away that a row can be written in.
 */
class WhereARuleDividesIsNotHowItWasWrittenTest {

    private static final LevelSpace WHOLE = LevelSpace.onACarrier(new Carrier.Whole());

    private static Level at(String number) {
        return new Level.OnACarrier(new Carrier.Whole(), new Count(new java.math.BigDecimal(number)));
    }

    /**
     * The two ways of writing one division of the whole numbers come to one seam.
     *
     * <p>Named by the two values it parts and not by either rule's threshold. Four is the last value
     * below and five the first value above, whichever of the two comparisons an author reached for.
     */
    @Test
    void twoOperatorsOverTheWholeNumbersDivideThemInOnePlace() {
        Seam closed = Seam.of(WHOLE, at("4"), Towards.BELOW);
        Seam open = Seam.of(WHOLE, at("5"), Towards.ABOVE);

        assertEquals(at("4"), closed.below(), "four is the last value `n <= 4` keeps");
        assertEquals(at("5"), closed.above(), "and five the first one it gives away");
        assertEquals(closed.key(), open.key(), "n < 5 parts them in the same place");
    }

    /**
     * What makes two seams one seam is where the values part, and not how the number was written.
     *
     * <p>{@code invariant value >= 0.00} and {@code guard x <= 0m} part a carrier's values in one
     * place. Told apart by their spelling they are two seams, and then a position has two classes
     * both holding zero — which is not a partition, and the classifier that reads a row against it
     * has no answer. The same rule {@link Level#key()} states, asked of a division rather than of a
     * value.
     */
    @Test
    void twoSpellingsOfOneNumberPartTheValuesInOnePlace() {
        assertEquals(Seam.of(WHOLE, at("0"), Towards.BELOW).key(),
                Seam.of(WHOLE, at("0.00"), Towards.BELOW).key(),
                "0 and 0.00 are one number and one place to part them");
        assertNotEquals(Seam.of(WHOLE, at("0"), Towards.BELOW).key(),
                Seam.of(WHOLE, at("1"), Towards.BELOW).key(),
                "and two places to part them are two seams");
    }

    /**
     * And over a carrier whose values fill, they do not.
     *
     * <p>The same two operators, and now nothing lies between the thresholds to be shared: the rule
     * that keeps its own value has a last value below and no first value above, and the rule that
     * gives it away has the opposite. Made one, a report would lose the distinction the two rules
     * actually draw.
     */
    @Test
    void theSameTwoOperatorsOverDecimalsDivideThemInTwoPlaces() {
        LevelSpace decimals = LevelSpace.onACarrier(new Carrier.Dense());
        Level half = new Level.OnACarrier(new Carrier.Dense(),
                new Count(new java.math.BigDecimal("0.5")));

        Seam closed = Seam.of(decimals, half, Towards.BELOW);
        Seam open = Seam.of(decimals, half, Towards.ABOVE);

        assertEquals(half, closed.below(), "`<= 0.5` keeps 0.5 on the lower side");
        assertEquals(null, closed.above(), "and a decimal names no value one step over it");
        assertEquals(null, open.below(), "`< 0.5` gives 0.5 away, and names no value one step back");
        assertEquals(half, open.above());
        assertNotEquals(closed.key(), open.key(),
                "the two rules part the decimals in different places");
    }

    /**
     * A division with no value either side of it is still a division, and two of them are still two.
     *
     * <p>{@code 3 * d} takes every third of a finite decimal and no whole number of thirds, so
     * neither the greatest value under one nor the least over it is a value this language writes.
     * That is what the border of {@code 3 * d <= 1} already says — it owes no row against its line
     * — and it leaves the values parted all the same. Told apart by the two values either side, two
     * such rules are one seam and the run between them disappears.
     */
    @Test
    void twoDivisionsWithNoValueEitherSideOfThemAreStillTwo() {
        LevelSpace thirds = LevelSpace.overFiniteDecimals(new java.math.BigDecimal("3"));
        Seam one = Seam.of(thirds, count("1"), Towards.BELOW);
        Seam two = Seam.of(thirds, count("2"), Towards.BELOW);

        assertEquals(null, one.below(), "no finite decimal is the greatest one under a third");
        assertEquals(null, one.above(), "and none is the least one over it");
        assertNotEquals(one.key(), two.key(),
                "and the two rules still part the values in two places");
    }

    /**
     * A rule written in twos parts the whole numbers where one written in ones does.
     *
     * <p>{@code 2 * n <= 9} and {@code n <= 4} are one division. Read as a form over {@code 2 * n},
     * the first parts the even numbers between eight and ten — which is the same place, said in the
     * units the rule was written in. Turning it back is exact: every level the written form attains
     * is a multiple of what it wrote, so nothing rounds.
     */
    @Test
    void aRuleWrittenInTwosPartsTheWholeNumbersWhereOneWrittenInOnesDoes() {
        java.math.BigDecimal two = new java.math.BigDecimal("2");
        Seam plain = Seam.of(WHOLE, at("4"), Towards.BELOW);
        Seam scaled = Seam.of(LevelSpace.steppingBy(two), count("9"), Towards.BELOW,
                new Seam.Scale(two, new Carrier.Whole()));

        assertEquals("4", scaled.below().key(), "eight of a doubled position is four of it");
        assertEquals("5", scaled.above().key());
        assertEquals(plain.key(), scaled.key(), "and the two rules part the values in one place");
    }

    /**
     * And two rules over thirds part the decimals in one place, where neither names a value.
     *
     * <p>{@code 3 * d <= 1} and {@code 6 * d <= 2} are one division at a third, which no finite
     * decimal is. Neither side names a value, so where they part can only be said as the place
     * itself — and said in the units each rule was written in, one is a third and the other is two
     * sixths. Told apart by those, a position would carry two lines at one place and a run between
     * them holding nothing.
     */
    @Test
    void twoRulesOverThirdsPartTheDecimalsInOnePlace() {
        java.math.BigDecimal three = new java.math.BigDecimal("3");
        java.math.BigDecimal six = new java.math.BigDecimal("6");
        LevelSpace thirds = LevelSpace.overFiniteDecimals(
                LevelSpace.generatorOverFiniteDecimals(three));
        LevelSpace sixths = LevelSpace.overFiniteDecimals(
                LevelSpace.generatorOverFiniteDecimals(six));

        Seam one = Seam.of(thirds, count("1"), Towards.BELOW,
                new Seam.Scale(three, new Carrier.Dense()));
        Seam two = Seam.of(sixths, count("2"), Towards.BELOW,
                new Seam.Scale(six, new Carrier.Dense()));

        assertEquals(null, one.below(), "a third is no finite decimal, so neither side names one");
        assertEquals(one.key(), two.key(), "and a third is two sixths");
    }

    /**
     * Whether a line keeps its own value is asked in the quantity's units, not the rule's.
     *
     * <p>{@code 2 * n <= 8} keeps four and {@code 2 * n <= 9} keeps nothing — nine halved is no
     * whole number, so the line falls between four and five and neither of them is on it. Held
     * against the level the rule was written with, both answered no: eight is not four. What reads
     * this is the order two lines at one place are put in, and the run either side of a line, so an
     * answer from the wrong units puts a value on the wrong side of the line it is on.
     */
    @Test
    void whetherALineKeepsItsOwnValueIsAskedInTheQuantitysUnits() {
        java.math.BigDecimal two = new java.math.BigDecimal("2");
        Seam.Scale scale = new Seam.Scale(two, new Carrier.Whole());
        LevelSpace evens = LevelSpace.steppingBy(two);

        assertEquals(true,
                Seam.of(evens, count("8"), Towards.BELOW, scale).keepsItsOwnValueBelow(),
                "`2 * n <= 8` is a line at four, and four is on the lower side of it");
        assertEquals(false,
                Seam.of(evens, count("9"), Towards.BELOW, scale).keepsItsOwnValueBelow(),
                "`2 * n <= 9` is a line between four and five, and neither is on it");
    }

    private static Level count(String number) {
        return new Level.ACount(new Count(new java.math.BigDecimal(number)));
    }
}
