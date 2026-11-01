package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.test.Allocated;

import java.math.BigInteger;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operation asked again of the operands it was asked of hands out the answer it gave, and makes
 * nothing for it: not the answer, not the ratio, not the parts. So does an order. What is kept is
 * only what is no wider than a bound and is a value, so an answer past the bound or none is worked
 * out again.
 */
class AnOperationAskedAgainOfItsOperandsMakesNothingTest {

    private static ExactRatio ratio(long numerator, long denominator) {
        return ExactRatio.of(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator));
    }

    private static final ExactRatio THIRD = ratio(1, 3);
    private static final ExactRatio SEVEN_HALVES = ratio(7, 2);

    private static final int ASKS = 2_000;

    /** The bytes {@code asking} allocates over {@link #ASKS} asks the second time they are run, the
     *  first having made whatever is made once — the answer, and the code loaded and linked. */
    private static long allocatedAskingAgain(Supplier<Object> asking) {
        Object first = asking.get();
        Runnable askingAgain = () -> {
            for (int i = 0; i < ASKS; i++) {
                assertSame(first, asking.get());
            }
        };
        askingAgain.run();
        return Allocated.byWhichMayBeNothing(askingAgain);
    }

    private static void makesNothing(String what, Supplier<Object> asking) {
        long allocated = allocatedAskingAgain(asking);
        assertTrue(allocated < ASKS, what + " asked again allocates nothing per ask, and " + allocated
                + " bytes were allocated for " + ASKS + " asks");
    }

    @Test
    void aSumAskedAgainMakesNothing() {
        makesNothing("a sum", () -> THIRD.plus(SEVEN_HALVES));
        assertEquals(ratio(23, 6), THIRD.plus(SEVEN_HALVES).orNull());
    }

    @Test
    void aProductAskedAgainMakesNothing() {
        makesNothing("a product", () -> THIRD.times(SEVEN_HALVES));
        assertEquals(ratio(7, 6), THIRD.times(SEVEN_HALVES).orNull());
    }

    @Test
    void aQuotientAskedAgainMakesNothing() {
        makesNothing("a quotient", () -> THIRD.dividedBy(SEVEN_HALVES));
        assertEquals(ratio(2, 21), THIRD.dividedBy(SEVEN_HALVES).orNull());
    }

    @Test
    void aDifferenceAskedAgainMakesNothing() {
        makesNothing("a difference", () -> THIRD.minus(SEVEN_HALVES));
        assertEquals(ratio(-19, 6), THIRD.minus(SEVEN_HALVES).orNull());
    }

    @Test
    void aNegationAskedAgainMakesNothing() {
        makesNothing("a negation", SEVEN_HALVES::negated);
        assertEquals(ratio(-7, 2), SEVEN_HALVES.negated());
        assertEquals(SEVEN_HALVES, SEVEN_HALVES.negated().negated(), "the negation of the negation is this");
    }

    /** Two values whose exponents are far apart are ordered by brackets of a working width and not in
     *  longs, and that order asked again makes nothing either. */
    @Test
    void anOrderAskedAgainMakesNothing() {
        ExactRatio small = ExactRatio.tenTo(-30);
        makesNothing("an order", () -> THIRD.compareTo(small));
        assertTrue(THIRD.compareTo(small) > 0);
        assertTrue(small.compareTo(THIRD) < 0, "the other way round is another pair");
    }

    /** An answer the operation gives without the arithmetic — a sum with nought, a product with one
     *  or nought, a quotient of nought or by one — is an answer all the same, and asked again makes
     *  nothing either. */
    @Test
    void anAnswerWithoutTheArithmeticAskedAgainMakesNothing() {
        makesNothing("a sum with nought", () -> THIRD.plus(ExactRatio.ZERO));
        makesNothing("a sum of nought", () -> ExactRatio.ZERO.plus(THIRD));
        makesNothing("a product with one", () -> THIRD.times(ExactRatio.ONE));
        makesNothing("a product of one", () -> ExactRatio.ONE.times(THIRD));
        makesNothing("a product with nought", () -> THIRD.times(ExactRatio.ZERO));
        makesNothing("a quotient of nought", () -> ExactRatio.ZERO.dividedBy(THIRD));
        makesNothing("a quotient by one", () -> THIRD.dividedBy(ExactRatio.ONE));
        assertEquals(THIRD, THIRD.plus(ExactRatio.ZERO).orNull());
        assertEquals(THIRD, ExactRatio.ONE.times(THIRD).orNull());
        assertEquals(ExactRatio.ZERO, THIRD.times(ExactRatio.ZERO).orNull());
        assertEquals(THIRD, THIRD.dividedBy(ExactRatio.ONE).orNull());
    }

    /** An order the arithmetic settles without brackets — by sign, or in longs — is not kept: pairs
     *  asked once each, as a sort asks them, make nothing at all. */
    @Test
    void anOrderSettledWithoutBracketsIsNotKept() {
        // the code is loaded and linked over pairs of its own, so that every pair measured is new
        comparingOnce(0).run();
        long allocated = Allocated.byWhichMayBeNothing(comparingOnce(ASKS));
        assertTrue(allocated < ASKS, "an order settled in longs makes nothing, and " + allocated
                + " bytes were allocated for " + ASKS + " pairs");
    }

    /** Pairs from {@code from} on, each asked once: one of them below nought every other time, so
     *  that some are settled by sign and the rest in longs. */
    private static Runnable comparingOnce(int from) {
        ExactRatio[] firsts = new ExactRatio[ASKS];
        ExactRatio[] seconds = new ExactRatio[ASKS];
        for (int i = 0; i < ASKS; i++) {
            firsts[i] = ratio(from + i + 1, 7);
            seconds[i] = i % 2 == 0 ? ratio(-(from + i + 2), 3) : ratio(from + i + 2, 3);
        }
        return () -> {
            for (int i = 0; i < ASKS; i++) {
                assertEquals(i % 2 == 0 ? 1 : -1, Integer.signum(firsts[i].compareTo(seconds[i])));
            }
        };
    }

    /** Operands wider than a long and within what is kept are kept as well. */
    @Test
    void aSumOfOperandsWiderThanALongAskedAgainMakesNothing() {
        ExactRatio wide = ExactRatio.of(BigInteger.TWO.pow(80).add(BigInteger.ONE), BigInteger.valueOf(3));
        makesNothing("a sum of wide operands", () -> wide.plus(THIRD));
        assertEquals(ExactRatio.of(BigInteger.TWO.pow(80).add(BigInteger.TWO), BigInteger.valueOf(3)),
                wide.plus(THIRD).orNull());
    }

    /** The order is part of the pair: the quotient the other way round is another answer. */
    @Test
    void aQuotientTheOtherWayRoundIsItsOwnAnswer() {
        for (int i = 0; i < 3; i++) {
            assertEquals(ratio(2, 21), THIRD.dividedBy(SEVEN_HALVES).orNull());
            assertEquals(ratio(21, 2), SEVEN_HALVES.dividedBy(THIRD).orNull());
            assertEquals(ratio(-19, 6), THIRD.minus(SEVEN_HALVES).orNull());
            assertEquals(ratio(19, 6), SEVEN_HALVES.minus(THIRD).orNull());
        }
    }

    /** Far more pairs than the tables have slots, so most are pushed out and many share a set. */
    @Test
    void everyPairIsGivenItsOwnAnswerWhateverIsKept() {
        for (int round = 0; round < 2; round++) {
            for (int n = 1; n <= 3_000; n++) {
                ExactRatio a = ratio(n, 7);
                ExactRatio b = ratio(3, n);
                assertEquals(ratio(n * n + 21, 7L * n), a.plus(b).orNull(), a + " + " + b);
                assertEquals(ratio(3, 7), a.times(b).orNull(), a + " * " + b);
                assertEquals(ratio((long) n * n, 21), a.dividedBy(b).orNull(), a + " / " + b);
            }
        }
    }

    /** Two operands far apart in scale have a sum of as many digits as they are apart, which is past
     *  the size kept, so it is worked out at every ask. */
    @Test
    void anAnswerTooWideToKeepIsWorkedOutAgain() {
        ExactRatio tiny = ExactRatio.tenTo(-1_000);
        ExactAnswer<ExactRatio> sum = ExactRatio.ONE.plus(tiny);
        assertEquals(ExactRatio.ONE.plus(tiny), sum);
        assertTrue(allocatedAskingAgainEqual(() -> ExactRatio.ONE.plus(tiny)) >= ASKS,
                "a sum of a thousand digits is not kept");
    }

    /** An answer that is no value is not kept: that the host had no room is a fact about the run that
     *  asked, and the answer is asked again. */
    @Test
    void anAnswerThatIsNoValueIsAskedAgain() {
        ExactRatio huge = ExactRatio.tenTo(Long.MAX_VALUE);
        assertEquals(ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS), huge.times(huge));
        assertTrue(allocatedAskingAgainEqual(() -> huge.times(huge)) >= ASKS,
                "an answer that is no value is not kept");
    }

    private static long allocatedAskingAgainEqual(Supplier<Object> asking) {
        Object first = asking.get();
        Runnable askingAgain = () -> {
            for (int i = 0; i < ASKS; i++) {
                assertEquals(first, asking.get());
            }
        };
        askingAgain.run();
        return Allocated.byWhichMayBeNothing(askingAgain);
    }
}
