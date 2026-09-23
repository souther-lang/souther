package souther.exact;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The readings an order is made of, each asked directly.
 *
 * <p>A comparison reaches the last of its readings only for pairs whose fractions no host has room to
 * write out, which is a pair no test builds. So what is held here is the readings themselves: that a
 * bracket too narrow for a pair says so rather than answering, that the refinement answers the pairs the
 * readings above it would have, and that the search for a width retreats into what the host holds. The
 * comparison's answers over the same values are held where the values are read from, by the types that
 * carry them.
 */
class TheOrdersInstrumentsAnswerWhatTheyAreAskedTest {

    private static final BigInteger FIVE = BigInteger.valueOf(5);

    private static final ExactParts COMPACT = parts(BigInteger.ONE, BigInteger.ONE, -1_000_000_000, -1_000_000_000);

    private static ExactParts parts(BigInteger numerator, BigInteger denominator, long twos, long fives) {
        return ExactArithmetic.canonical(numerator, denominator, twos, fives);
    }

    private static ExactParts ratio(BigInteger numerator, BigInteger denominator) {
        return parts(numerator, denominator, 0, 0);
    }

    /** A power of two against the power of five that comes nearest it, both far past what a machine
     *  holds. The two exponents are a very good whole-number approximation of {@code log2 5}, so the two
     *  logs sit a tiny fraction of a bit apart and no count of bits separates them. */
    private static ExactParts aPowerOfTwo() {
        return parts(BigInteger.ONE, BigInteger.ONE, 3_086_630_039_907_612_845L, 0);
    }

    private static ExactParts theNearestPowerOfFive() {
        return parts(BigInteger.ONE, BigInteger.ONE, 0, 1_329_339_201_633_350_533L);
    }

    @Test
    void aBracketSeparatesTwoValuesWhoseExponentsAreApart() {
        assertEquals(Integer.valueOf(-1),
                ExactOrder.magnitudeFromBrackets(COMPACT, ratio(BigInteger.ONE, BigInteger.ONE), 128));
    }

    /** The same pair the comparison answers is undecided at a narrow width, so the width rising is what
     *  reaches the answer and not a first bracket that was always going to be enough. */
    @Test
    void aBracketTooNarrowToSeparateAPairSaysSo() {
        ExactParts twos = aPowerOfTwo();
        ExactParts fives = theNearestPowerOfFive();

        assertNull(ExactOrder.magnitudeFromBrackets(twos, fives, 64));
        assertNull(ExactOrder.magnitudeFromBrackets(fives, twos, 64));
        assertEquals(Integer.valueOf(1), ExactOrder.magnitudeFromBrackets(twos, fives, 128));
    }

    @Test
    void aPairInsideTheStartingWidthIsSeparatedByTheNextOne() {
        ExactParts aPower = parts(BigInteger.ONE, BigInteger.ONE, 0, 100);
        ExactParts oneAbove = ratio(FIVE.pow(100).add(BigInteger.ONE), BigInteger.ONE);

        assertNull(ExactOrder.magnitudeFromBrackets(aPower, oneAbove, ExactOrder.BRACKET_BITS));
        assertEquals(Integer.valueOf(-1), ExactOrder.magnitudeFromBrackets(aPower, oneAbove, 256));
    }

    /** Two fractions of one size a part in that size apart stand closer than any width settled before
     *  they arrive, so no bracket of the starting width separates them. */
    @Test
    void twoFractionsOfOneSizeAreLeftOpenByTheStartingBracket() {
        BigInteger base = BigInteger.TWO.pow(700);
        ExactParts lower = ratio(base.add(BigInteger.ONE), base.add(BigInteger.valueOf(3)));
        ExactParts higher = ratio(base.add(BigInteger.valueOf(11)), base.add(BigInteger.valueOf(13)));

        assertNull(ExactOrder.magnitudeFromBrackets(lower, higher, ExactOrder.BRACKET_BITS));
        assertEquals(-1, ExactOrder.magnitudeByRefining(lower, higher));
        assertEquals(1, ExactOrder.magnitudeByRefining(higher, lower));
    }

    @Test
    void twoWhosePowersDifferAreLeftOpenByTheStartingBracketToo() {
        BigInteger odd = BigInteger.TWO.pow(700).add(BigInteger.ONE);
        ExactParts justBelowTwo = ratio(odd.shiftLeft(1).subtract(BigInteger.ONE), odd);
        ExactParts two = parts(BigInteger.ONE, BigInteger.ONE, 1, 0);

        assertNull(ExactOrder.magnitudeFromBrackets(justBelowTwo, two, ExactOrder.BRACKET_BITS));
        assertEquals(-1, ExactOrder.magnitudeByRefining(justBelowTwo, two));
    }

    @Test
    void anExponentAStoredDenominatorCancelsIsLeftOpenByTheStartingBracket() {
        BigInteger power = BigInteger.TWO.pow(4000);
        ExactParts justBelowOne = parts(BigInteger.ONE, power.add(BigInteger.ONE), 4000, 0);

        assertNull(ExactOrder.magnitudeFromBrackets(
                justBelowOne, ratio(BigInteger.ONE, BigInteger.ONE), ExactOrder.BRACKET_BITS));
    }

    @Test
    void aValueAFactorOfFiveFromHalfIsLeftOpenByTheStartingBracket() {
        BigInteger odd = BigInteger.TWO.pow(700).add(BigInteger.ONE);
        ExactParts justBelowHalf = parts(odd, odd.multiply(BigInteger.TEN).add(BigInteger.ONE), 0, 1);
        ExactParts half = parts(BigInteger.ONE, BigInteger.ONE, -1, 0);

        assertNull(ExactOrder.magnitudeFromBrackets(justBelowHalf, half, ExactOrder.BRACKET_BITS));
    }

    @Test
    void aValueAPartInItsOwnSizeFromHalfIsLeftOpenByTheStartingBracket() {
        BigInteger base = BigInteger.TWO.pow(700);
        ExactParts justBelowHalf = parts(
                base.add(BigInteger.valueOf(3)), base.add(BigInteger.valueOf(7)), -1, 0);
        ExactParts half = parts(BigInteger.ONE, BigInteger.ONE, -1, 0);

        assertNull(ExactOrder.magnitudeFromBrackets(justBelowHalf, half, ExactOrder.BRACKET_BITS));
    }

    @Test
    void theRefinementAnswersAPairTheStartingWidthLeavesOpenAtTheExponentsItStandsAt() {
        ExactParts aPower = parts(BigInteger.ONE, BigInteger.ONE, 0, 100);
        ExactParts oneAbove = ratio(FIVE.pow(100).add(BigInteger.ONE), BigInteger.ONE);

        assertNull(ExactOrder.magnitudeFromBrackets(aPower, oneAbove, ExactOrder.BRACKET_BITS));
        assertEquals(-1, ExactOrder.magnitudeByRefining(aPower, oneAbove));
    }

    /**
     * Over values small enough to spell out, the order the refinement answers is the order the whole
     * numbers do.
     *
     * <p>The pairs it is reached for cannot be checked against a second reading, there being no second
     * reading of a pair no machine writes out. So it is checked where both are possible and asked for
     * directly, over a grid of numerators, denominators and both exponents, in both directions. What that
     * holds is the refinement itself: that a bracket holds the number it was taken for however many times
     * it has been cut, and that the rising ends where the pair comes apart rather than where it is equal.
     */
    @Test
    @Timeout(60)
    void theOrderTheRefinementAnswersIsTheOrderTheWholeNumbersDo() {
        List<ExactParts> values = new ArrayList<>();
        for (long n : new long[] {1, 3, 7, -3}) {
            for (long d : new long[] {1, 2, 7}) {
                for (long twos : new long[] {-2, 0, 3}) {
                    for (long fives : new long[] {-2, 0, 3}) {
                        values.add(parts(BigInteger.valueOf(n), BigInteger.valueOf(d), twos, fives));
                    }
                }
            }
        }

        for (ExactParts a : values) {
            for (ExactParts b : values) {
                int exactly = up(a).abs().multiply(down(b)).compareTo(up(b).abs().multiply(down(a)));
                if (exactly == 0) {
                    // Two of one magnitude are one value, which the comparison answers before any
                    // reading is reached, and a bracket holding both never separates them.
                    continue;
                }
                assertEquals(Integer.signum(exactly), ExactOrder.magnitudeByRefining(a, b),
                        a + " against " + b);
            }
        }
    }

    /**
     * A pair of huge opposing exponents is written out by neither side.
     *
     * <p>Both values are one exponent each; the two exponents are large and pull opposite ways, so the
     * writing that puts their difference on one side asks for a power of two of some three hundred million
     * megabytes and a power of five of the same. Neither is a number the host holds, so both writings
     * decline, which nothing else here would notice, the order being settled for this pair by the cheap
     * bracket before any writing is reached.
     */
    @Test
    void aPairOfHugeOpposingExponentsIsWrittenOutByNeitherSide() {
        ExactParts twos = aPowerOfTwo();
        ExactParts fives = theNearestPowerOfFive();

        assertNull(ExactOrder.magnitudeWrittenOut(twos, fives, Long.MAX_VALUE));
        assertNull(ExactOrder.magnitudeWrittenOut(fives, twos, Long.MAX_VALUE));
        assertTrue(ExactArithmetic.compare(twos, fives) > 0);
    }

    /**
     * A power of two against a power of five brought within a hundred and thirty bits of it by a
     * fraction: one pair with every part of the shape in it.
     *
     * <p>Compact, with large exponents pulling opposite ways so that neither writing is a number the host
     * holds, and closer together than the width the comparison starts at. So the comparison reaches the
     * refinement by its own route, with nothing standing in for anything. The fraction is the correction,
     * computed apart from this and checked by what it does: the starting width does not separate the pair
     * and twice it does.
     */
    @Test
    void aPowerOfTwoAndACorrectedPowerOfFiveReachTheRefinementByThemselves() {
        ExactParts twos = aPowerOfTwo();
        ExactParts correctedFives = parts(
                new BigInteger("1393796574908163946434124475858836208137477"),
                new BigInteger("1393796574908163946345982392040522594123779"),
                0, 1_329_339_201_633_350_533L);

        assertNull(ExactOrder.magnitudeFromBrackets(twos, correctedFives, ExactOrder.BRACKET_BITS));
        assertEquals(Integer.valueOf(1), ExactOrder.magnitudeFromBrackets(twos, correctedFives, 256));
        assertNull(ExactOrder.magnitudeWrittenOut(twos, correctedFives, Long.MAX_VALUE));
        assertNull(ExactOrder.magnitudeWrittenOut(correctedFives, twos, Long.MAX_VALUE));

        assertTrue(ExactArithmetic.compare(twos, correctedFives) > 0);
        assertTrue(ExactArithmetic.compare(correctedFives, twos) < 0);
    }

    /**
     * A pair the starting width leaves open, whose powers no writing is worth, is answered by refining,
     * through the comparison's own readings and not by asking the last of them directly.
     *
     * <p>What stands in for the host's end here is the budget, the reading being told no writing is worth
     * anything. The route is then the route the huge pair takes: bracket open, both writings declining,
     * the refinement answering. The answer is held against cross multiplication, which these are small
     * enough for.
     */
    @Test
    void aPairNoWritingIsWorthIsAnsweredByTheReadingsBelowIt() {
        BigInteger power = FIVE.pow(300);
        BigInteger[] near = theBestApproximationOf(power, BigInteger.TWO.pow(697), 135);
        ExactParts aPower = parts(BigInteger.ONE, BigInteger.ONE, 0, 300);
        ExactParts nearIt = parts(near[0], near[1], 697, 0);

        assertNull(ExactOrder.magnitudeFromBrackets(aPower, nearIt, ExactOrder.BRACKET_BITS));
        assertNull(ExactOrder.magnitudeWrittenOut(aPower, nearIt, 0));

        int exactly = power.multiply(near[1]).compareTo(near[0].multiply(BigInteger.TWO.pow(697)));
        assertEquals(Integer.signum(exactly), ExactOrder.magnitudeWithAWritingWorth(aPower, nearIt, 0));
        assertEquals(-Integer.signum(exactly), ExactOrder.magnitudeWithAWritingWorth(nearIt, aPower, 0));
        assertEquals(Integer.signum(exactly), Integer.signum(ExactArithmetic.compare(aPower, nearIt)));
    }

    /**
     * The best approximation of {@code n/d} whose denominator is over {@code bits} bits, as a numerator
     * beside a denominator.
     *
     * <p>The convergents of the walk a common measure takes, which are the closest any fraction of their
     * size stands to what they approximate.
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
     * The search for a width retreats into what the host holds where the rise has asked for too much.
     *
     * <p>Two searches are going on in the refinement and they are not the same search: one is for the
     * precision the question needs, which rises, and the other is for where the host's room gives out,
     * which is only found by asking. Read as one, the first width that asked for too much ended the whole
     * thing, so a question needing a width between the last one that was held and the one that failed went
     * unanswered while the room for it was there, which is the one thing a total order may not do.
     *
     * <p>Asked of the mechanism with a reading of its own, because for any reading of a value the two
     * widths stand hundreds of megabytes apart.
     */
    @Test
    void theSearchForAWidthRetreatsIntoWhatTheHostHolds() {
        int enough = 5000;
        int pastWhatIsHeld = 6000;
        List<Integer> tried = new ArrayList<>();

        String answered = ExactOrder.asWideAsItTakes(width -> {
            tried.add(width);
            if (width >= pastWhatIsHeld) {
                throw new ExactRoomExceeded("no room for a width of " + width);
            }
            return width >= enough ? "answered" : null;
        }, () -> "answer this");

        assertEquals("answered", answered);
        assertTrue(tried.stream().anyMatch(width -> width >= pastWhatIsHeld),
                "the rise asked for a width the host would not hold, which is what the retreat is for");
        assertTrue(tried.stream().anyMatch(width -> width >= enough && width < pastWhatIsHeld),
                "and the answer came from a width between the two");
    }

    /** Where no width the host holds is wide enough the search ends and the run has failed. The two widths
     *  close on one another, so it stops rather than going round for ever. */
    @Test
    @Timeout(20)
    void whereNoWidthTheHostHoldsIsEnoughTheRunHasFailed() {
        assertThrows(ExactRoomExceeded.class, () -> ExactOrder.asWideAsItTakes(
                width -> {
                    if (width >= 6000) {
                        throw new ExactRoomExceeded("no room for a width of " + width);
                    }
                    return null;
                },
                () -> "answer this"));
    }

    /**
     * A count of bits past what the host addresses is the run's shortage, not a number.
     *
     * <p>A width and a bit length are both counted in an {@code int}, so a count made of two of them wraps
     * in silence, and a wrapped count of bits does not refuse but answers, a negative shift being a shift
     * the other way. What came of that was a bracket holding the wrong numbers, which is an order answered
     * wrongly rather than declined. Reaching it through a comparison wants numbers of some hundreds of
     * megabytes, so the arithmetic that every count goes through is asked directly.
     */
    @Test
    void aCountOfBitsPastWhatTheHostAddressesIsTheRunsShortage() {
        assertEquals(Integer.MAX_VALUE, ExactPowers.bitsTheHostAddresses(Integer.MAX_VALUE));
        assertThrows(ExactRoomExceeded.class,
                () -> ExactPowers.bitsTheHostAddresses(Integer.MAX_VALUE + 1L));
        assertThrows(ExactRoomExceeded.class,
                () -> ExactPowers.bitsTheHostAddresses((long) Integer.MAX_VALUE + Integer.MAX_VALUE));
    }

    private static BigInteger up(ExactParts r) {
        return r.numerator().multiply(power(r.twos(), BigInteger.TWO))
                .multiply(power(r.fives(), FIVE));
    }

    private static BigInteger down(ExactParts r) {
        return r.denominator().multiply(power(-r.twos(), BigInteger.TWO))
                .multiply(power(-r.fives(), FIVE));
    }

    private static BigInteger power(long exponent, BigInteger of) {
        return exponent <= 0 ? BigInteger.ONE : of.pow((int) exponent);
    }
}
