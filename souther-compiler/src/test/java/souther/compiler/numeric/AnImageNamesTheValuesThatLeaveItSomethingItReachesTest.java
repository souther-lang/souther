package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an image is asked for when a value has to be chosen rather than rejected.
 *
 * <p>{@link AdditiveImage#contains} answers about a residue that already exists. A search choosing
 * where one position stands has no residue yet, and the values worth choosing are the ones leaving
 * the rest something they reach — the same arithmetic, asked as a set.
 *
 * <p>Held here rather than through a search. What comes back is a coset, and a coset is either right
 * or wrong about infinitely many values; a search reaching a row says one of them was right.
 */
class AnImageNamesTheValuesThatLeaveItSomethingItReachesTest {

    private static Rational at(long whole) {
        return Rational.of(whole);
    }

    /** Every value the answer names does leave a residue the image reaches. */
    private static void leavesSomethingReached(AdditiveImage image, Rational coefficient,
                                               Rational target, AffinePreimage answer) {
        for (long step = -3; step <= 3; step++) {
            Rational x = switch (answer) {
                case AffinePreimage.None ignored -> null;
                case AffinePreimage.Stepping on -> on.from().plus(on.by().times(at(step)));
                // A tenth of the generator is a finite decimal, so it is a member and it is not one
                // a progression would have named.
                case AffinePreimage.Filling on ->
                        on.from().plus(on.by().times(new Rational(BigInteger.valueOf(step),
                                BigInteger.TEN)));
            };
            if (x != null) {
                assertTrue(image.contains(target.minus(coefficient.times(x))),
                        "at " + x + " the residue is " + target.minus(coefficient.times(x)));
            }
        }
    }

    /**
     * The case #916 is about. {@code 3a + 6b = 3} asks {@code 3 - 3a} to be a multiple of six, which
     * is {@code a} odd — and the value a search takes off an unbounded range is zero.
     */
    @Test
    void aPositionUnderACongruenceIsNamedByTheClassItSolves() {
        AdditiveImage rest = new AdditiveImage.OverWholeNumbers(at(6));

        AffinePreimage answer = rest.affinePreimage(at(3), at(3), Granularity.DISCRETE);

        assertEquals(new AffinePreimage.Stepping(at(1), at(2)), answer);
        leavesSomethingReached(rest, at(3), at(3), answer);
    }

    /** No value of it leaves one, and that is a proof rather than a search that found nothing. */
    @Test
    void aPositionWhoseCoefficientCannotReachTheResidueIsNamedByNothing() {
        AdditiveImage rest = new AdditiveImage.OverWholeNumbers(at(4));

        assertInstanceOf(AffinePreimage.None.class,
                rest.affinePreimage(at(2), at(1), Granularity.DISCRETE));
    }

    /** A weight below zero is the same question, and the class it names is still written from it. */
    @Test
    void aWeightBelowZeroNamesTheSameValues() {
        AdditiveImage rest = new AdditiveImage.OverWholeNumbers(at(6));

        AffinePreimage answer = rest.affinePreimage(at(-3), at(3), Granularity.DISCRETE);

        assertEquals(new AffinePreimage.Stepping(at(1), at(2)), answer);
        leavesSomethingReached(rest, at(-3), at(3), answer);
    }

    /**
     * Where the values fill, the answer is dense and is not every value.
     *
     * <p>{@code a + 3b = 1} over decimals: a search taking zero for {@code a} asks for a third of
     * {@code b}, which is not a decimal a model writes. One is, and so is {@code 1.3} — and two is
     * not.
     */
    @Test
    void aPositionWhoseValuesFillIsNamedByACosetAndNotByEveryValue() {
        AdditiveImage rest = new AdditiveImage.OverFiniteDecimals(at(3));

        AffinePreimage answer = rest.affinePreimage(at(1), at(1), Granularity.DENSE);

        assertEquals(new AffinePreimage.Filling(at(1), at(3)), answer);
        leavesSomethingReached(rest, at(1), at(1), answer);
    }

    /**
     * Two and five drop out of what the position is held to, and three does not.
     *
     * <p>What decides it is the denominator of the weight against the generator, not the weight. A
     * position weighed three halves against a generator of three contributes half of every decimal,
     * and half of every decimal is every decimal — two is a unit among them — so it is held to
     * nothing. Weighed one against the same generator it contributes thirds, and a third is not a
     * decimal a model writes, so it is held to a coset of three.
     *
     * <p>The same reduction {@link AdditiveImage.OverFiniteDecimals} makes of its own generator, and
     * made here because making it in one place and not the other is what would let the two disagree.
     */
    @Test
    void theUnitsOfTheFiniteDecimalsAreNotAThingAPositionIsHeldTo() {
        AdditiveImage rest = new AdditiveImage.OverFiniteDecimals(at(3));

        AffinePreimage byHalves =
                rest.affinePreimage(new Rational(BigInteger.valueOf(3), BigInteger.TWO), at(3),
                        Granularity.DENSE);
        assertEquals(new AffinePreimage.Filling(Rational.ZERO, Rational.ONE), byHalves);
        leavesSomethingReached(rest, new Rational(BigInteger.valueOf(3), BigInteger.TWO), at(3),
                byHalves);

        assertEquals(new AffinePreimage.Filling(at(1), at(3)),
                rest.affinePreimage(at(1), at(1), Granularity.DENSE));
    }

    /**
     * One coset is one value however the inverse that found it came out.
     *
     * <p>Two members are one where their difference is the generator times a decimal, and a tenth is
     * a decimal — so a coset of three holds {@code 1} and {@code 1.3} as one member and not as two.
     * Taking whole multiples of the generator away instead, the arithmetic answered a target of one
     * and a target of thirteen tenths with different values of the same set, and a search that tries
     * one member of a dense coset would try a different value depending on which it started from.
     */
    @Test
    void aCosetComesBackAtTheSameMemberHoweverItWasFound() {
        AdditiveImage rest = new AdditiveImage.OverFiniteDecimals(at(3));

        assertEquals(new AffinePreimage.Filling(Rational.ZERO, at(3)),
                rest.affinePreimage(at(2), at(6), Granularity.DENSE));
        assertEquals(rest.affinePreimage(Rational.ONE, at(1), Granularity.DENSE),
                rest.affinePreimage(Rational.ONE,
                        Rational.of(new java.math.BigDecimal("1.3")), Granularity.DENSE));
        assertEquals(new AffinePreimage.Filling(Rational.ONE, at(3)),
                new AffinePreimage.Filling(
                        Rational.of(new java.math.BigDecimal("1.3")), at(3)));
        assertEquals(new AffinePreimage.Stepping(at(1), at(2)),
                new AffinePreimage.Stepping(at(7), at(2)));
    }

    /**
     * Taking the units out of a value answers for every value, which it did not when it was a helper
     * of one caller.
     *
     * <p>Nothing divides into zero, or everything does — either way what is left of it is itself,
     * and a loop looking for the last factor of two in it does not end. The caller this was written
     * for had refused zero before it asked, and moving it onto {@link Rational} took the body and
     * left the refusal behind.
     */
    @Test
    void takingTheUnitsOutOfAValueAnswersForEveryValue() {
        assertEquals(Rational.ZERO, Rational.ZERO.unitsRemoved());
        assertEquals(at(3), at(3).unitsRemoved());
        assertEquals(Rational.ONE, at(20).unitsRemoved());
        // One below zero is a unit as well, so three and minus three generate the same decimals.
        assertEquals(at(3), at(-3).unitsRemoved());
    }

    /** And a generator the decimals treat as nothing is nothing: two is a unit among them, so a
     *  coset of two is every decimal there is. */
    @Test
    void aGeneratorMadeOfUnitsHoldsEveryDecimal() {
        assertEquals(new AffinePreimage.Filling(Rational.ZERO, Rational.ONE),
                new AffinePreimage.Filling(Rational.ZERO, at(2)));
    }
}
