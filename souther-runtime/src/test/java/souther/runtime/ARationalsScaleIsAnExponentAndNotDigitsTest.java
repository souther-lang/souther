package souther.runtime;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That a decimal's scale reaches a rational as an exponent, and that what is done with the value
 * afterwards does not build the power the scale names.
 *
 * <p>The scales here are ones whose power of ten has no representation a machine holds — a scale of a
 * billion asks for a number of some four hundred megabytes — so a step that built one would not
 * finish rather than finishing slowly. That is the positive control: every assertion below is reached
 * only by an implementation that left the scale an exponent.
 */
class ARationalsScaleIsAnExponentAndNotDigitsTest {

    /** A decimal written as one digit and a scale, which is eleven characters and not a billion. */
    private static final BigDecimal COMPACT = new BigDecimal(BigInteger.ONE, 1_000_000_000);

    private static final BigInteger FIVE = BigInteger.valueOf(5);

    @Test
    void aScaleBecomesTwoExponentsAndNoDigits() {
        Rational taken = Rational.of(COMPACT);
        assertEquals(BigInteger.ONE, taken.numerator());
        assertEquals(BigInteger.ONE, taken.denominator());
        assertEquals(-1_000_000_000, taken.twos());
        assertEquals(-1_000_000_000, taken.fives());
    }

    @Test
    void multiplyingAndDividingMoveTheExponentsAndBuildNothing() {
        Rational taken = Rational.of(COMPACT);
        Rational squared = taken.times(taken);
        assertEquals(-2_000_000_000, squared.twos());
        assertEquals(-2_000_000_000, squared.fives());
        assertEquals(Rational.ONE, taken.dividedBy(taken));
        assertEquals(taken, squared.dividedBy(taken));
        assertEquals(1_000_000_000, taken.reciprocal().twos());
    }

    /**
     * Every decimal has one of these, including the one whose scale has no positive counterpart.
     *
     * <p>The widening is a rule and not a range this type happens to cover: a scale is thirty-two bits
     * and enters as its negation, so an exponent of the same width would refuse the least scale there
     * is. This is the value that says the two widths are not the same question.
     */
    @Test
    void theLeastScaleThereIsWidensLikeAnyOther() {
        Rational taken = Rational.of(new BigDecimal(BigInteger.ONE, Integer.MIN_VALUE));

        assertEquals(2147483648L, taken.twos());
        assertEquals(2147483648L, taken.fives());
        assertEquals(BigInteger.ONE, taken.numerator());
    }

    /** An exponent is sixty-four bits, and a product asking for more of it aborts rather than
     *  answering about a value it cannot hold. */
    @Test
    void anExponentPastWhatIsHeldAborts() {
        Rational far = new Rational(BigInteger.ONE, BigInteger.ONE, Long.MAX_VALUE, 0);

        assertThrows(ConstraintViolation.class, () -> far.times(far));
    }

    /** And a product whose exponents merely add is exact, however far past a scale's own width they
     *  run — which is the control for the abort above. */
    @Test
    void aProductPastWhatAScaleHoldsIsStillExact() {
        Rational taken = Rational.of(COMPACT);
        Rational squared = taken.times(taken);

        assertEquals(-2_000_000_000L, squared.twos());
        assertEquals(-4_000_000_000L, squared.times(squared).twos());
    }

    /**
     * And narrowing it back to a decimal keeps the power of ten as a scale.
     *
     * <p>The way out is part of the same promise as the way in. Multiplied into the digits instead, a
     * compact decimal that entered exact arithmetic paid for every digit of its scale on the way back
     * out — a billion of them here, which is why this assertion is reached only by an implementation
     * that moved the power to the scale.
     */
    @Test
    void narrowingBackToADecimalMovesThePowerToTheScale() {
        Rational taken = Rational.of(COMPACT);

        assertEquals(COMPACT, RationalMath.toDecimal(1_000_000_000, HALF_UP.INSTANCE, taken));
    }

    /** A millionth of a millionth against one: the two are nowhere near each other, so the brackets
     *  the comparison starts with separate them and no power is built. */
    @Test
    void aComparisonIsDecidedFromTheExponentsWhereTheValuesAreApart() {
        Rational taken = Rational.of(COMPACT);
        assertEquals(Integer.valueOf(-1), taken.magnitudeFromBrackets(Rational.ONE, 128));
        assertTrue(taken.compareTo(Rational.ONE) < 0);
        assertTrue(Rational.ONE.compareTo(taken) > 0);
        assertTrue(taken.compareTo(taken.negated()) > 0);
        assertEquals(0, taken.compareTo(Rational.of(COMPACT)));
    }

    /**
     * A power of two against the power of five that comes nearest it, both far past what a machine
     * holds.
     *
     * <p>This is the pair the order is hardest to answer for, and it is the pair the whole of the
     * comparison's shape is owed to. The two exponents are a very good whole-number approximation of
     * {@code log2 5} — the five-exponent is the denominator of one, the two-exponent its numerator — so
     * the two logs sit a tiny fraction of a bit apart. A bracket read off counts of bits can never
     * separate that, however many digits the numbers have; and the numbers have far more digits than a
     * machine holds, so nothing can fall back to them. Both values are one exponent each and the answer
     * is one of three, so an order that refused here would be refusing over an intermediate.
     */
    private static Rational aPowerOfTwo() {
        return new Rational(BigInteger.ONE, BigInteger.ONE, 3_086_630_039_907_612_845L, 0);
    }

    /** And the power of five just below it. */
    private static Rational theNearestPowerOfFive() {
        return new Rational(BigInteger.ONE, BigInteger.ONE, 0, 1_329_339_201_633_350_533L);
    }

    @Test
    void aPowerOfTwoAndTheNearestPowerOfFiveAreOrdered() {
        Rational twos = aPowerOfTwo();
        Rational fives = theNearestPowerOfFive();

        assertTrue(twos.compareTo(fives) > 0, "the power of two is the greater of the two");
        assertTrue(fives.compareTo(twos) < 0);
        assertEquals(0, twos.compareTo(aPowerOfTwo()));
        assertTrue(twos.negated().compareTo(fives.negated()) < 0);
    }

    /**
     * And a bracket too narrow to separate that pair says so rather than answering.
     *
     * <p>The control for the refinement: the same pair the comparison answers is undecided at a width
     * the exponents' own is, so the width rising is what reaches the answer and not a first bracket that
     * was always going to be enough. A bracket that always decided would leave the loop above it
     * unreached, and one that never did would leave the comparison looping.
     */
    @Test
    void aBracketTooNarrowToSeparateAPairSaysSo() {
        Rational twos = aPowerOfTwo();
        Rational fives = theNearestPowerOfFive();

        assertNull(twos.magnitudeFromBrackets(fives, 64));
        assertNull(fives.magnitudeFromBrackets(twos, 64));
        assertEquals(Integer.valueOf(1), twos.magnitudeFromBrackets(fives, 128));
    }

    /**
     * A pair the width the comparison starts at cannot separate, which is what the width rises for.
     *
     * <p>A power of five, and the whole number one above it. The power is large enough that a bracket of
     * the starting width has to drop bits off it, and the two values are one part in the whole number
     * apart — far inside what dropping those bits leaves. So the first bracket overlaps and the answer
     * comes from the next, which is the only way a pair this close is answered at all.
     */
    @Test
    void aPairInsideTheStartingWidthIsAnsweredByRaisingIt() {
        Rational aPower = new Rational(BigInteger.ONE, BigInteger.ONE, 0, 100);
        Rational oneAbove = new Rational(FIVE.pow(100).add(BigInteger.ONE), BigInteger.ONE, 0, 0);

        assertNull(aPower.magnitudeFromBrackets(oneAbove, 128),
                "the width the comparison starts at does not separate this pair");
        assertEquals(Integer.valueOf(-1), aPower.magnitudeFromBrackets(oneAbove, 256));

        assertTrue(aPower.compareTo(oneAbove) < 0, "and the comparison reaches that width");
        assertTrue(oneAbove.compareTo(aPower) > 0);
    }

    /**
     * And over values small enough to spell out, the order the brackets answer is the order the whole
     * numbers do.
     *
     * <p>The brackets are where every comparison is decided, including the ordinary ones, and each of
     * them is built by a division that rounds, a shift that drops bits, and a pair of ends cut to a
     * width. So the answer over values where a second reading is possible is held against that reading:
     * the exact one, by multiplying the powers out and cross-multiplying, which these are small enough
     * for and no value this type holds is in general. Every pair over a grid of numerators, denominators
     * and both exponents, in both directions.
     *
     * <p>Held to a time as well. A bracket that did not hold the number it is about would leave pairs it
     * never separates, and the width rising through every count of bits there is takes long enough to
     * read as a run that stopped rather than one that failed.
     */
    @Test
    @Timeout(60)
    void theOrderTheBracketsAnswerIsTheOrderTheWholeNumbersDo() {
        List<Rational> values = new ArrayList<>();
        for (long n : new long[] {1, 3, 7, -1, -3}) {
            for (long d : new long[] {1, 2, 3, 7}) {
                for (long twos : new long[] {-2, 0, 3}) {
                    for (long fives : new long[] {-2, 0, 3}) {
                        values.add(new Rational(
                                BigInteger.valueOf(n), BigInteger.valueOf(d), twos, fives));
                    }
                }
            }
        }

        for (Rational a : values) {
            for (Rational b : values) {
                // the exact order, by cross-multiplying the two values spelled out as fractions
                int exactly = up(a).multiply(down(b)).compareTo(up(b).multiply(down(a)));
                assertEquals(Integer.signum(exactly), Integer.signum(a.compareTo(b)),
                        a + " against " + b);
            }
        }
    }

    /**
     * Two fractions of the same powers, a part in their own size apart, are ordered.
     *
     * <p>Which no bracket settled ahead of them can do. Two fractions of some many bits stand as close as
     * a part in that many bits twice over, and the width a bracket is taken at is chosen before the pair
     * arrives — so a bracket is the wrong instrument for this shape however wide it is taken, and the
     * assertion below says the one the comparison starts at does not reach it.
     *
     * <p>What answers is that the powers here are the same on both sides. They cancel, and what is left is
     * a fraction against a fraction, which is answered exactly by the walk a common measure takes: whole
     * parts compared, then the remainders the other way about. No width, and no product of any two of the
     * four numbers either.
     */
    @Test
    void twoFractionsOfOneSizeAndTheSamePowersAreOrdered() {
        BigInteger base = BigInteger.TWO.pow(700);
        Rational lower = Rational.of(base.add(BigInteger.ONE), base.add(BigInteger.valueOf(3)));
        Rational higher = Rational.of(base.add(BigInteger.valueOf(11)), base.add(BigInteger.valueOf(13)));
        assertEquals(0, lower.twos(), "the powers cancel, which is what the shape is about");
        assertEquals(0, higher.fives());

        assertNull(lower.magnitudeFromBrackets(higher, 128),
                "no bracket of the width the comparison starts at separates these");
        assertTrue(lower.compareTo(higher) < 0, "and the order is answered all the same");
        assertTrue(higher.compareTo(lower) > 0);
        assertEquals(0, lower.compareTo(
                Rational.of(base.add(BigInteger.ONE), base.add(BigInteger.valueOf(3)))));
    }

    /**
     * And so are two whose powers differ, which is the same shape with a factor left in it.
     *
     * <p>Two below two, by a part in a large number, against two exactly: the exponents are not the same on
     * the two sides, so nothing cancels, and the closeness is still the fractions' own. What answers is
     * that the power between them can be written down — so it is written down, and what is left is one
     * fraction against another. Gating that on the powers happening to cancel would have left this pair to
     * a width, and no width settled on before a pair arrives reaches a pair as close as it likes.
     */
    @Test
    void twoWhosePowersDifferAreOrderedByWritingThePowerDown() {
        BigInteger odd = BigInteger.TWO.pow(700).add(BigInteger.ONE);
        Rational justBelowTwo = Rational.of(odd.shiftLeft(1).subtract(BigInteger.ONE), odd);
        Rational two = new Rational(BigInteger.ONE, BigInteger.ONE, 1, 0);
        assertTrue(justBelowTwo.twos() != two.twos() || justBelowTwo.fives() != two.fives(),
                "the powers do not cancel, which is what this is about");

        assertNull(justBelowTwo.magnitudeFromBrackets(two, 128),
                "no bracket of the width the comparison starts at separates these");
        assertTrue(justBelowTwo.compareTo(two) < 0, "and the order is answered all the same");
        assertTrue(two.compareTo(justBelowTwo) > 0);
    }

    /**
     * And a value whose exponent a stored denominator cancels, which no width settles either.
     *
     * <p>A power of two over one more than itself: the exponent is far past what a bracket is taken to, and
     * the denominator is the same size, so the two all but cancel and the value sits a part in that size
     * below one. Neither the exponent's own size nor the fraction's says anything useful here — what
     * decides is whether the value written out is a whole number the host holds, and it is, because the
     * power is the size of a denominator that is already stored.
     *
     * <p>The exponent here is one a power can be written down at, so this pair is answered whether the
     * decision reads the exponent or the value. What it pins is the shape, not the reading: the pair the
     * two readings part company over needs a denominator of a hundred megabytes, which is past what a test
     * holds and not past what the type does.
     */
    @Test
    void anExponentAStoredDenominatorCancelsIsOrderedToo() {
        BigInteger power = BigInteger.TWO.pow(4000);
        Rational justBelowOne = new Rational(BigInteger.ONE, power.add(BigInteger.ONE), 4000, 0);
        assertEquals(4000L, justBelowOne.twos(), "the exponent no bracket reaches");

        assertNull(justBelowOne.magnitudeFromBrackets(Rational.ONE, 128));
        assertTrue(justBelowOne.compareTo(Rational.ONE) < 0, "and the order is answered all the same");
        assertTrue(Rational.ONE.compareTo(justBelowOne) > 0);
        assertEquals(1L, RationalMath.toInt(HALF_UP.INSTANCE, justBelowOne));
        assertEquals(0L, RationalMath.toInt(DOWN.INSTANCE, justBelowOne));
    }

    /** And the rounding of such a value, a factor of five standing between it and half of one. */
    @Test
    void aValueAFactorOfFiveFromHalfOfOneRoundsByThePolicy() {
        BigInteger odd = BigInteger.TWO.pow(700).add(BigInteger.ONE);
        Rational justBelowHalf = new Rational(
                odd, odd.multiply(BigInteger.TEN).add(BigInteger.ONE), 0, 1);
        Rational half = new Rational(BigInteger.ONE, BigInteger.ONE, -1, 0);
        assertEquals(1L, justBelowHalf.fives(), "a power of five stands in it");
        assertNull(justBelowHalf.magnitudeFromBrackets(half, 128));
        assertTrue(justBelowHalf.compareTo(half) < 0);

        assertEquals(0L, RationalMath.toInt(HALF_UP.INSTANCE, justBelowHalf));
        assertEquals(1L, RationalMath.toInt(UP.INSTANCE, justBelowHalf));
    }

    /**
     * And a value a part in its own size below half of one rounds to whichever neighbour the policy says.
     *
     * <p>The same shape reaching the narrowing: which of two whole numbers a value rounds to is where it
     * stands against half way, and a value this close to half way is past what a bracket reaches. Here too
     * no power of five stands between, so twice the value is a fraction and its whole part is exact.
     */
    @Test
    void aValueJustBelowHalfOfOneRoundsByThePolicyAndNotByAWidth() {
        BigInteger base = BigInteger.TWO.pow(700);
        Rational justBelowHalf = new Rational(
                base.add(BigInteger.valueOf(3)), base.add(BigInteger.valueOf(7)), -1, 0);
        Rational half = new Rational(BigInteger.ONE, BigInteger.ONE, -1, 0);
        assertNull(justBelowHalf.magnitudeFromBrackets(half, 128),
                "no bracket of that width tells this from half of one");

        assertEquals(0L, RationalMath.toInt(HALF_UP.INSTANCE, justBelowHalf));
        assertEquals(0L, RationalMath.toInt(HALF_EVEN.INSTANCE, justBelowHalf));
        assertEquals(1L, RationalMath.toInt(UP.INSTANCE, justBelowHalf));
        assertEquals(0L, RationalMath.toInt(DOWN.INSTANCE, justBelowHalf));
    }

    /**
     * And the rounding the brackets answer is the rounding the digits do.
     *
     * <p>The narrowing reads the same bracket the order does, so it is held against a second reading the
     * same way: over values small enough to spell out, the whole number it answers is the one a decimal
     * built from those digits and rounded by the host answers. Every policy, at scales on both sides of
     * nought, for values above and below one and on either side of nought.
     */
    @Test
    @Timeout(60)
    void theRoundingTheBracketsAnswerIsTheRoundingTheDigitsDo() {
        for (long n : new long[] {1, 3, 7, 25, -1, -3, -25}) {
            for (long d : new long[] {1, 2, 3, 7}) {
                for (long twos : new long[] {-4, -1, 0, 2}) {
                    for (long fives : new long[] {-3, 0, 1}) {
                        Rational r = new Rational(
                                BigInteger.valueOf(n), BigInteger.valueOf(d), twos, fives);
                        // Far more places than the scales asked for below. A value that stands exactly
                        // half way at one of those scales is one that ends, and one that ends is exact
                        // here — so the rounding of the reading is the rounding of the value.
                        BigDecimal spelled = new BigDecimal(up(r))
                                .divide(new BigDecimal(down(r)), 60, java.math.RoundingMode.HALF_UP);
                        for (java.math.RoundingMode towards : java.math.RoundingMode.values()) {
                            if (towards == java.math.RoundingMode.UNNECESSARY) {
                                continue;
                            }
                            for (int scale : new int[] {-1, 0, 1, 3}) {
                                assertEquals(spelled.setScale(scale, towards), r.asDecimal(scale, towards),
                                        r + " at scale " + scale + " " + towards);
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * And asking for a decimal the value does not reach while naming no rounding is the caller's mistake,
     * not the host running out of room.
     *
     * <p>Which of the two it is said to be is the point. The abort a whole number too large leaves by is an
     * exception of the host's arithmetic, translated at the operation into this language's own — so a policy
     * refused the same way came back saying no Rational held a whole number that size, which is untrue of
     * the value, of the answer, and of the machine.
     */
    @Test
    void namingNoRoundingWhereRoundingIsNeededIsTheCallersMistake() {
        Rational aThird = Rational.of(BigInteger.ONE, BigInteger.valueOf(3));

        assertThrows(IllegalArgumentException.class,
                () -> aThird.asDecimal(3, java.math.RoundingMode.UNNECESSARY));
        // and a value that is the decimal asked for is answered without a policy being read at all
        assertEquals(new BigDecimal("0.25"), Rational.of(BigInteger.ONE, BigInteger.valueOf(4))
                .asDecimal(2, java.math.RoundingMode.UNNECESSARY));
    }

    /**
     * And asking the order the other way about answers, and answers the other way.
     *
     * <p>Not only the sign but the answering. Writing a pair out to compare it exactly is a different pair
     * of whole numbers depending on which of the two the difference of the exponents is put on, so the room
     * one writing needs is not the room the other does — and an order that took one writing and stopped
     * would answer a pair one way round and refuse it the other. Which of the two values was asked about
     * is not a fact about the pair, so it cannot decide whether the pair has an order.
     */
    @Test
    @Timeout(60)
    void askingTheOrderTheOtherWayAboutAnswersTheOtherWay() {
        List<Rational> values = new ArrayList<>();
        for (long n : new long[] {1, 3, 7, -1}) {
            for (long d : new long[] {1, 3, 7}) {
                for (long twos : new long[] {-30, -1, 0, 4000}) {
                    for (long fives : new long[] {-2, 0, 1}) {
                        values.add(new Rational(
                                BigInteger.valueOf(n), BigInteger.valueOf(d), twos, fives));
                    }
                }
            }
        }

        for (Rational a : values) {
            for (Rational b : values) {
                int forward = Integer.signum(a.compareTo(b));
                int backward = Integer.signum(b.compareTo(a));
                assertEquals(forward, -backward, a + " against " + b + " both ways about");
            }
        }
    }

    /**
     * And the refinement on its own answers the pairs the readings above it answer.
     *
     * <p>It is the reading the order's promise is made of: the three above it are cheap and each is allowed
     * to decline, and this one asks for no width in advance and so has nothing to decline for. Asked
     * through a comparison it is unreachable to a fixture — the pairs that reach it are the ones whose
     * fractions the host has no room to write out, which is a pair no test builds — so it is asked here
     * directly, on the pairs the readings above it would have taken.
     *
     * <p>Each of these is undecided at the width the comparison starts at, which is the control: the answer
     * below is one the width rising reached and not one the first bracket had. Take the rising away and this
     * is what says so.
     */
    @Test
    @Timeout(60)
    void theRefinementAnswersAPairTheStartingWidthLeavesOpen() {
        BigInteger base = BigInteger.TWO.pow(700);
        Rational lower = Rational.of(base.add(BigInteger.ONE), base.add(BigInteger.valueOf(3)));
        Rational higher = Rational.of(base.add(BigInteger.valueOf(11)), base.add(BigInteger.valueOf(13)));
        assertNull(lower.magnitudeFromBrackets(higher, 128),
                "the width the comparison starts at does not separate these");
        assertEquals(-1, lower.magnitudeByRefining(higher));
        assertEquals(1, higher.magnitudeByRefining(lower));

        Rational aPower = new Rational(BigInteger.ONE, BigInteger.ONE, 0, 100);
        Rational oneAbove = new Rational(FIVE.pow(100).add(BigInteger.ONE), BigInteger.ONE, 0, 0);
        assertNull(aPower.magnitudeFromBrackets(oneAbove, 128));
        assertEquals(-1, aPower.magnitudeByRefining(oneAbove));
    }

    /**
     * And over values small enough to spell out, the order the refinement answers is the order the whole
     * numbers do.
     *
     * <p>The pairs it is reached for cannot be checked against a second reading, there being no second
     * reading of a pair no machine writes out. So it is checked where both readings are possible and asked
     * for directly: every pair over a grid of numerators, denominators and both exponents, against the
     * exact order of the two spelled out, in both directions. What that holds is the refinement itself —
     * that a bracket holds the number it was taken for however many times it has been cut, and that the
     * rising ends where the pair comes apart rather than where the pair is equal.
     */
    @Test
    @Timeout(60)
    void theOrderTheRefinementAnswersIsTheOrderTheWholeNumbersDo() {
        List<Rational> values = new ArrayList<>();
        for (long n : new long[] {1, 3, 7, -3}) {
            for (long d : new long[] {1, 2, 7}) {
                for (long twos : new long[] {-2, 0, 3}) {
                    for (long fives : new long[] {-2, 0, 3}) {
                        values.add(new Rational(
                                BigInteger.valueOf(n), BigInteger.valueOf(d), twos, fives));
                    }
                }
            }
        }

        for (Rational a : values) {
            for (Rational b : values) {
                // the exact order of the two magnitudes, by cross-multiplying them spelled out
                int exactly = up(a).abs().multiply(down(b)).compareTo(up(b).abs().multiply(down(a)));
                if (exactly == 0) {
                    // Two of one magnitude are one record and one sign, which the comparison answers
                    // before any reading is reached — and a bracket, holding both, never separates them.
                    continue;
                }
                assertEquals(Integer.signum(exactly), a.magnitudeByRefining(b),
                        a + " against " + b);
            }
        }
    }

    /**
     * A pair of huge opposing exponents is written out by neither side, and is still ordered.
     *
     * <p>This is the pair #1795 is about, read at the reading that was its whole subject. Both values are
     * one exponent each; the two exponents are large and pull opposite ways, so the writing that puts their
     * difference on one side asks for a power of two of some three hundred million megabytes on the way up
     * and a power of five of the same on the way down. Neither is a number the host holds, so both writings
     * decline — which is the fact this asserts, and which nothing else here would notice, the order being
     * settled for this pair by the cheap bracket before any writing is reached.
     */
    @Test
    void aPairOfHugeOpposingExponentsIsWrittenOutByNeitherSide() {
        Rational twos = aPowerOfTwo();
        Rational fives = theNearestPowerOfFive();

        assertNull(twos.magnitudeWrittenOut(fives, Long.MAX_VALUE),
                "no writing of this pair is a number the host holds, whatever it may cost");
        assertNull(fives.magnitudeWrittenOut(twos, Long.MAX_VALUE));
        assertTrue(twos.compareTo(fives) > 0, "and the order is answered all the same");
    }

    /**
     * And a pair the starting width leaves open, whose powers no writing is worth, is answered by refining —
     * through the comparison's own readings and not by asking the last of them directly.
     *
     * <p>The pair has everything the shape needs but the size: compact parts, large exponents pulling
     * opposite ways, and the two values standing far closer together than the width the comparison starts
     * at. What it does not have is powers past what the host holds, because a pair with those has no second
     * reading to check the answer against — so what stands in for the host's end here is the budget, the
     * reading being told no writing is worth anything. The route is then the route the huge pair takes:
     * bracket open, both writings declining, the refinement answering.
     *
     * <p>The fraction is the best one of its size standing near the power, so the two values agree over
     * hundreds of bits — found by the walk a common measure takes, which is the same walk that orders two
     * fractions. The answer is held against cross multiplication, which these are small enough for.
     */
    @Test
    void aPairNoWritingIsWorthIsAnsweredByTheReadingsBelowIt() {
        BigInteger power = FIVE.pow(300);
        BigInteger[] near = theBestApproximationOf(power, BigInteger.TWO.pow(697), 135);
        Rational aPower = new Rational(BigInteger.ONE, BigInteger.ONE, 0, 300);
        Rational nearIt = new Rational(near[0], near[1], 697, 0);

        assertNull(aPower.magnitudeFromBrackets(nearIt, 128),
                "the width the comparison starts at does not separate this pair");
        assertNull(aPower.magnitudeWrittenOut(nearIt, 0),
                "and no writing of it is worth taking at this budget");

        // the exact order, by cross-multiplying the two written out as fractions
        int exactly = power.multiply(near[1]).compareTo(near[0].multiply(BigInteger.TWO.pow(697)));
        assertEquals(Integer.signum(exactly), aPower.magnitudeWithAWritingWorth(nearIt, 0));
        assertEquals(-Integer.signum(exactly), nearIt.magnitudeWithAWritingWorth(aPower, 0));
        // and the same pair, left to work out for itself what a writing is worth, answers the same
        assertEquals(Integer.signum(exactly), Integer.signum(aPower.compareTo(nearIt)));
    }

    /**
     * The best approximation of {@code n/d} whose denominator is over {@code bits} bits, as a numerator
     * beside a denominator.
     *
     * <p>The convergents of the walk a common measure takes, which are the closest any fraction of their
     * size stands to what they approximate — a denominator of some many bits lands within twice that many
     * bits of the value, which is how a fixture stands hundreds of bits from a power while staying small
     * enough to read.
     */
    private static BigInteger[] theBestApproximationOf(BigInteger n, BigInteger d, int bits) {
        BigInteger overBefore = BigInteger.ZERO;
        BigInteger over = BigInteger.ONE;
        BigInteger underBefore = BigInteger.ONE;
        BigInteger under = BigInteger.ZERO;
        BigInteger up = n;
        BigInteger by = d;
        while (under.bitLength() <= bits && by.signum() != 0) {
            BigInteger[] step = up.divideAndRemainder(by);
            BigInteger overNext = step[0].multiply(over).add(overBefore);
            BigInteger underNext = step[0].multiply(under).add(underBefore);
            overBefore = over;
            over = overNext;
            underBefore = under;
            under = underNext;
            up = by;
            by = step[1];
        }
        return new BigInteger[] {over, under};
    }

    /**
     * And the search for a width retreats into what the host holds where the rise has asked for too much.
     *
     * <p>Two searches are going on in the refinement and they are not the same search: one is for the
     * precision the question needs, which rises, and the other is for where the host's room gives out, which
     * is only found by asking. Read as one, the first width that asked for too much ended the whole thing —
     * so a question needing a width between the last one that was held and the one that failed went
     * unanswered while the room for it was there, which is the one thing a total order may not do.
     *
     * <p>Asked of this mechanism with a reading of its own, because for any reading of a Rational the two
     * widths stand hundreds of megabytes apart. The rising overshoots by design, which is what the assertion
     * below the answer says: the width that failed was tried, and the answer came from a narrower one.
     */
    @Test
    void theSearchForAWidthRetreatsIntoWhatTheHostHolds() {
        int enough = 5000;
        int pastWhatIsHeld = 6000;
        List<Integer> tried = new ArrayList<>();

        String answered = Rational.asWideAsItTakes(width -> {
            tried.add(width);
            if (width >= pastWhatIsHeld) {
                throw new OutOfRoom("no room for a width of " + width);
            }
            return width >= enough ? "answered" : null;
        }, () -> "answer this");

        assertEquals("answered", answered);
        assertTrue(tried.stream().anyMatch(width -> width >= pastWhatIsHeld),
                "the rise asked for a width the host would not hold, which is what the retreat is for");
        assertTrue(tried.stream().anyMatch(width -> width >= enough && width < pastWhatIsHeld),
                "and the answer came from a width between the two");
    }

    /**
     * And where no width the host holds is wide enough, the search ends and the run has failed.
     *
     * <p>The control for the retreat, and what says it ends: the two widths close on one another, so the
     * search stops rather than going round for ever. A retreat that could not end would have been the other
     * way to lose the promise.
     */
    @Test
    @Timeout(20)
    void whereNoWidthTheHostHoldsIsEnoughTheRunHasFailed() {
        assertThrows(OutOfRoom.class, () -> Rational.asWideAsItTakes(
                width -> {
                    if (width >= 6000) {
                        throw new OutOfRoom("no room for a width of " + width);
                    }
                    return null;
                },
                () -> "answer this"));
    }

    /**
     * And a count of bits past what the host addresses is the run's shortage, not a number.
     *
     * <p>A width and a bit length are both counted in an {@code int}, so a count made of two of them wraps
     * in silence — and a wrapped count of bits does not refuse but answers, a negative shift being a shift
     * the other way. What came of that was a bracket holding the wrong numbers, which is an order answered
     * wrongly rather than declined. Reaching it through a comparison wants numbers of some hundreds of
     * megabytes, so the arithmetic that every count goes through is asked directly.
     */
    @Test
    void aCountOfBitsPastWhatTheHostAddressesIsTheRunsShortage() {
        assertEquals(Integer.MAX_VALUE, Rational.bitsTheHostAddresses(Integer.MAX_VALUE));
        assertThrows(OutOfRoom.class, () -> Rational.bitsTheHostAddresses(Integer.MAX_VALUE + 1L));
        assertThrows(OutOfRoom.class,
                () -> Rational.bitsTheHostAddresses((long) Integer.MAX_VALUE + Integer.MAX_VALUE));
    }

    /** The numerator of a value spelled out as one fraction, which only the small ones can be. */
    private static BigInteger up(Rational r) {
        return r.numerator().multiply(power(r.twos(), BigInteger.TWO))
                .multiply(power(r.fives(), FIVE));
    }

    /** And its denominator, which is above nought, so cross-multiplying keeps the order. */
    private static BigInteger down(Rational r) {
        return r.denominator().multiply(power(-r.twos(), BigInteger.TWO))
                .multiply(power(-r.fives(), FIVE));
    }

    /** {@code of^exponent} where the exponent is above nought, and one where it is not. */
    private static BigInteger power(long exponent, BigInteger of) {
        return exponent <= 0 ? BigInteger.ONE : of.pow((int) exponent);
    }

    /** And a small close pair is answered too, where the numbers themselves are what the brackets are
     *  built from. */
    @Test
    void aSmallCloseValueIsOrderedAsWell() {
        Rational aThird = Rational.of(BigInteger.ONE, BigInteger.valueOf(3));
        Rational aLittleMore = Rational.of(BigInteger.valueOf(334), BigInteger.valueOf(1000));

        assertTrue(aThird.compareTo(aLittleMore) < 0);
        assertTrue(aLittleMore.compareTo(aThird) > 0);
        assertTrue(Rational.of(1).compareTo(Rational.of(1000)) < 0);
    }

    /** A value too large to read is described rather than spelled, and the description is the size of
     *  what is stored. */
    @Test
    void aValueTooLargeToSpellIsDescribed() {
        assertEquals("1/1×2^-1000000000×5^-1000000000", Rational.of(COMPACT).toString());
        assertEquals("1/2", Rational.of(BigInteger.ONE, BigInteger.TWO).toString());
        assertEquals("2", Rational.of(4).dividedBy(Rational.of(2)).toString());
        assertEquals("-1/3", Rational.of(-1).dividedBy(Rational.of(3)).toString());
    }
}
