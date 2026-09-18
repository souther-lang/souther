package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Towards;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A quantity whose own lattice is over a number no decimal writes takes its own values.
 *
 * <p><b>A fractional cut on a whole-numbered lattice and a fractional lattice are two things.</b>
 * {@code 3 * d <= 1} puts a line at a third on an order whose values are thirds of a decimal, and
 * the line is a place the quantity has no value at. {@code 1 / 3 * x < 2} over whole {@code x} is
 * the other one: the quantity takes the values a third apart, so a third is a value it has. A
 * geometry that carried its cut exactly and its lattice in decimals would pass the first and fail
 * this, and the two have to be told apart for either to be right (ADR-0117).
 *
 * <p><b>Read at the places a run stops at, and not at the decimals beside them.</b> A run is written
 * against the lines the rules draw, and a line at a third is not a decimal. Narrowed to the nearest
 * decimal either side of it, {@code [1/3, 1/3]} closes onto a place the order has no value at and
 * comes back holding nothing — and that is a false answer about the order rather than a search that
 * gave up, because {@link LevelSpace#inspect} is what a proof is read off. Nothing downstream can
 * recover it either: an exact reading afterwards can only take values out of the set.
 *
 * <p>Which is a different question from whether a row can be written. Where a value of the quantity
 * has to become a value on a carrier, a third is none — and that is the edge {@link CutPosition}
 * and {@link souther.compiler.numeric.Count#at} answer at, not this one.
 */
class AnOrderWhoseOwnStepIsNoDecimalStillHasItsValuesTest {

    private static ExactRatio ratio(long over, long under) {
        return ExactRatio.of(java.math.BigInteger.valueOf(over),
                java.math.BigInteger.valueOf(under));
    }

    private static final ExactRatio A_THIRD = ratio(1, 3);

    private static final ExactRatio TWO_THIRDS = ratio(2, 3);

    private static final ExactRatio A_HALF = ratio(1, 2);

    private static Level at(ExactRatio number) {
        return new Level.OfTheQuantity(number);
    }

    /** The quantity a third apart stands at a third, which no decimal is. */
    @Test
    void aLatticeOverAThirdTakesAThird() {
        LevelSpace thirds = LevelSpace.steppingBy(A_THIRD);

        assertTrue(thirds.attainable(at(A_THIRD)),
                "a third is a multiple of a third, so this order stands there");
        assertInstanceOf(Occupancy.Inhabited.class,
                thirds.inspect(LevelInterval.point(at(A_THIRD))),
                "and the run that is that one place holds it");
    }

    /**
     * And it stands at no half, which is what says the reading above is the order's answer.
     *
     * <p>The control the rest of this rests on. An order that answered "inhabited" to every run
     * would pass the test above and say nothing, so the same reading is asked at a place this
     * lattice does not reach.
     */
    @Test
    void andTheSameLatticeTakesNoHalf() {
        LevelSpace thirds = LevelSpace.steppingBy(A_THIRD);

        assertFalse(thirds.attainable(at(A_HALF)),
                "a half is no whole number of thirds");
        assertEquals(new Occupancy.Empty(), thirds.inspect(LevelInterval.point(at(A_HALF))));
    }

    /**
     * A fractional cut on a whole-numbered lattice is the other case, and answers the other way.
     *
     * <p>Both are a line at a third. What differs is the quantity: one counts in thirds and the
     * other in whole numbers, and only the first has a value there.
     */
    @Test
    void aWholeNumberedLatticeTakesNoThird() {
        assertFalse(LevelSpace.steppingBy(ExactRatio.ONE).attainable(at(A_THIRD)),
                "the whole numbers are not a third apart, so the line falls between two of them");
        assertTrue(LevelSpace.steppingBy(ExactRatio.ONE).canCutAt(at(A_THIRD)),
                "and the line is still a line, which is the question the order answers yes to");
    }

    /** Its neighbours are its own values and not the decimals beside them. */
    @Test
    void theNeighboursOfAThirdAreThirds() {
        LevelSpace thirds = LevelSpace.steppingBy(A_THIRD);

        assertEquals(Optional.of(at(ExactRatio.ONE)),
                thirds.neighbour(at(TWO_THIRDS), Towards.ABOVE),
                "one is the value above two thirds on an order counting by thirds");
        assertEquals(Optional.of(at(A_THIRD)),
                thirds.neighbour(at(TWO_THIRDS), Towards.BELOW));
    }

    /**
     * A run between two of its values holds the ones between, and none where there are none.
     *
     * <p>Both ends are places no decimal is, so this is the reading that cannot be done in the
     * numbers a model writes at all.
     */
    @Test
    void aRunBetweenTwoThirdsHoldsWhatLiesBetweenThem() {
        LevelSpace thirds = LevelSpace.steppingBy(A_THIRD);

        Occupancy across = thirds.inspect(new LevelInterval(
                Bound.at(at(A_THIRD), true), Bound.at(at(ExactRatio.ONE), true)));
        assertEquals(new Occupancy.Inhabited(at(A_THIRD), at(ExactRatio.ONE)), across,
                "a third, two thirds and one, with its ends at the two it was written against");

        assertEquals(new Occupancy.Empty(), thirds.inspect(new LevelInterval(
                        Bound.at(at(A_THIRD), false), Bound.at(at(TWO_THIRDS), false))),
                "and nothing strictly between two values one step apart");
    }

    /** What this compiler can write down there is the value itself, not a decimal near it. */
    @Test
    void theWitnessOfSuchARunIsOneOfItsOwnValues() {
        LevelSpace thirds = LevelSpace.steppingBy(A_THIRD);

        Witness found = thirds.witness(LevelInterval.point(at(A_THIRD)), Towards.ABOVE);

        assertEquals(new Witness.Found(at(A_THIRD)), found);
    }

    /**
     * And where the positions fill, the same holds of the generator.
     *
     * <p>{@code 1 / 3 * d} takes every third of a finite decimal. A third is one of them — it is the
     * generator itself — and this is dense, so the run past it has no first value and every value.
     */
    @Test
    void aDenseLatticeOverAThirdTakesItsGenerator() {
        LevelSpace thirds = LevelSpace.overFiniteDecimals(A_THIRD);

        assertTrue(thirds.attainable(at(A_THIRD)));
        assertEquals(Optional.empty(), thirds.neighbour(at(A_THIRD), Towards.ABOVE),
                "what fills has no next value, which is a different answer from having none past it");
        assertTrue(thirds.anythingBeyond(at(A_THIRD), Towards.ABOVE));
    }
}
