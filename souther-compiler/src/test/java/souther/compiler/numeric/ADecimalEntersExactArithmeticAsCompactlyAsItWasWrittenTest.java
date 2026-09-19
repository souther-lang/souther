package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.Duration;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A decimal is compact where a model writes it, and entering the constraint algebra is not a reason
 * for it to stop being. A fraction with that decimal's denominator can be written, and writing it is
 * work proportional to the scale — so the question each of these asks is about the numbers held,
 * which is where the answer has to be rather than in how long a run happens to take.
 *
 * <p>Both directions, because the way out is where a bound becomes a number a reader is handed and
 * is therefore reached by every domain that answers one: a value taken in compactly and spelled out
 * on the way back has only moved the cost.
 */
@Timeout(value = 20, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
class ADecimalEntersExactArithmeticAsCompactlyAsItWasWrittenTest {

    /** A scale no run would finish at if the power of ten were built, and one a {@code Decimal}
     *  holds, so nothing here rests on the value being out of range. */
    private static final int WIDE = 1_000_000;

    private static final BigDecimal A_MILLIONTH_OF_A_MILLIONTH =
            BigDecimal.ONE.scaleByPowerOfTen(-WIDE);

    /** How many bits the numbers a compact value holds are allowed to take. Wide enough that a value
     *  a model wrote is nowhere near it, and far below what one digit per unit of scale would be. */
    private static final int FEW = 1024;

    /** A decimal written at a scale a model may write and no machine spells out. */
    private static final ExactRatio TOO_WIDE_TO_SPELL =
            ExactRatio.of(new BigDecimal(BigInteger.ONE, 16_000_000));

    private static void isCompact(ExactRatio ratio) {
        assertTrue(ratio.numeratorWithoutUnits().abs().bitLength() < FEW,
                () -> "the numerator holds " + ratio.numeratorWithoutUnits().bitLength() + " bits");
        assertTrue(ratio.denominatorWithoutUnits().bitLength() < FEW,
                () -> "the denominator holds "
                        + ratio.denominatorWithoutUnits().bitLength() + " bits");
    }

    @Test
    void aDecimalOfALargeScaleIsTakenInWithoutBuildingItsPowerOfTen() {
        ExactRatio embedded = ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH);
        isCompact(embedded);
        assertEquals(BigInteger.ONE, embedded.numeratorWithoutUnits());
        assertEquals(BigInteger.ONE, embedded.denominatorWithoutUnits());
        assertEquals(-WIDE, embedded.twos());
        assertEquals(-WIDE, embedded.fives());
    }

    @Test
    void theDecimalThatComesBackIsTheOneThatWentInAndIsAsCompact() {
        BigDecimal back = ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH).asWrittenDecimal();
        assertEquals(0, A_MILLIONTH_OF_A_MILLIONTH.compareTo(back));
        assertEquals(WIDE, back.scale());
        assertTrue(back.unscaledValue().bitLength() < FEW,
                () -> "the unscaled value holds " + back.unscaledValue().bitLength() + " bits");
    }

    @Test
    void theUnitsComeOutOfAWideScaleWithoutLookingForThemOneAtATime() {
        assertEquals(ExactRatio.ONE, ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH).unitsRemoved());
        assertEquals(BigInteger.ONE, ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH).spread());
    }

    @Test
    void arithmeticOverACompactDecimalLeavesItCompact() {
        ExactRatio wide = ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH);
        isCompact(wide.times(ExactRatio.of(7)));
        isCompact(wide.dividedBy(ExactRatio.of(7)));
        isCompact(wide.times(wide));
        isCompact(wide.negated());
        isCompact(wide.abs());
    }

    /**
     * A negative scale is the other value entirely, and the difference is the value's. The whole
     * number a decimal written as a multiple of a power of ten denotes genuinely has that many
     * digits, so what is owed is that nothing beyond holding it is built — which is what the two
     * exponents say.
     */
    @Test
    void aDecimalWrittenAsAMultipleOfAPowerOfTenIsHeldWithoutSpellingIt() {
        ExactRatio embedded = ExactRatio.of(BigDecimal.ONE.scaleByPowerOfTen(WIDE));
        isCompact(embedded);
        assertEquals(WIDE, embedded.twos());
        assertEquals(WIDE, embedded.fives());
        assertTrue(embedded.isWhole());
        assertEquals(0, embedded.compareTo(ExactRatio.of(BigDecimal.ONE.scaleByPowerOfTen(WIDE))));
        assertTrue(embedded.compareTo(ExactRatio.ONE) > 0);
    }

    /** What the compactness is not allowed to cost: the value is the value it was, and every answer
     *  about it is the answer a fraction would give. */
    @Test
    void theMeaningOfARatioIsWhatItWas() {
        ExactRatio third = ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3));
        ExactRatio half = ExactRatio.of(new BigDecimal("0.5"));
        assertEquals(ExactRatio.of(BigInteger.valueOf(5), BigInteger.valueOf(6)), third.plus(half));
        assertEquals(ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(6)),
                ExactRatio.gcd(third, half));
        assertEquals(ExactRatio.of(BigInteger.TWO, BigInteger.valueOf(3)), third.dividedBy(half));
        assertEquals("1/3", third.spelled());
        assertEquals("0.5", half.spelled());
        assertNull(third.asWrittenDecimal());
        assertEquals(new BigDecimal("0.5"), half.asWrittenDecimal().stripTrailingZeros());
        assertEquals(BigInteger.ZERO, third.floor());
        assertEquals(BigInteger.ONE, third.ceiling());
        assertEquals(BigInteger.ZERO, third.truncated());
        assertEquals(BigInteger.valueOf(-1), third.negated().floor());
        assertEquals(BigInteger.ZERO, third.negated().truncated());
        assertEquals(BigInteger.valueOf(3), ExactRatio.of(new BigDecimal("3.0")).truncated());
        assertTrue(ExactRatio.of(new BigDecimal("3.0")).isWhole());
        assertTrue(ExactRatio.of(new BigDecimal("30E-1")).isWhole());
    }

    /** Two writings of one value are one value, which a representation carrying exponents has to go
     *  on deciding: a map keyed by these answers on {@link ExactRatio#equals}. */
    @Test
    void oneValueIsOneRepresentationHoweverItArrived() {
        assertEquals(ExactRatio.of(new BigDecimal("0.5")),
                ExactRatio.of(BigInteger.ONE, BigInteger.TWO));
        assertEquals(ExactRatio.of(new BigDecimal("0.5")).hashCode(),
                ExactRatio.of(BigInteger.ONE, BigInteger.TWO).hashCode());
        assertEquals(ExactRatio.of(new BigDecimal("2.0")), ExactRatio.of(2));
        assertEquals(ExactRatio.of(new BigDecimal("20E-1")), ExactRatio.of(2));
        assertEquals(ExactRatio.ZERO, ExactRatio.of(new BigDecimal("0.000")));
        assertEquals(ExactRatio.of(BigInteger.valueOf(-1), BigInteger.valueOf(20)),
                ExactRatio.of(new BigDecimal("-0.05")));
    }

    /**
     * What the compactness is for, which nothing about the numbers held can be asked for.
     *
     * <p>The constructor puts a ratio in its canonical form whatever it was handed, so an embedding
     * that built the power of ten would answer with the same compact value — the numbers say nothing
     * about what was formed on the way to them. The cost is the only thing that tells the two apart,
     * and so the cost is what this holds.
     *
     * <p>The margin is why a wall clock is safe here: the work this does is a few microseconds and
     * an embedding proportional to the scale is minutes at this width, so nothing a machine varies
     * by stands between them.
     */
    @Test
    void takingADecimalInAndHandingItBackDoesNotCostWhatItsScaleSays() {
        assertTimeoutPreemptively(Duration.ofSeconds(10), () -> {
            ExactRatio embedded = ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH);
            assertEquals(0, A_MILLIONTH_OF_A_MILLIONTH.compareTo(embedded.asWrittenDecimal()));
            assertEquals(ExactRatio.ONE, embedded.unitsRemoved());
            assertTrue(embedded.compareTo(ExactRatio.ONE) < 0);
        });
    }

    /**
     * The way out, asked where every reader of a bound reaches it.
     *
     * <p>A domain answers a bound by handing back a number somebody can write, and that is the step
     * a value taken in compactly is spelled out at if the compactness stops at the door. So the
     * subject here is the domain and not the ratio: what comes back has to be the decimal that went
     * in, held the way it was written.
     */
    @Test
    void aBoundAtACompactDecimalIsHandedBackAsCompactlyAsItArrived() {
        NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .assume(LinearForm.<String>atom("a").minus(
                                LinearForm.constant(ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH))),
                        Rel.LE, Map.of("a", Granularity.DENSE));
        Endpoint most = domain.boundsOf("a").max();
        assertNotNull(most);
        BigDecimal at = ((Count) most.at()).at();
        assertEquals(0, A_MILLIONTH_OF_A_MILLIONTH.compareTo(at));
        assertTrue(at.unscaledValue().bitLength() < FEW,
                () -> "the bound came back over " + at.unscaledValue().bitLength() + " bits");
    }

    /**
     * A wide decimal through the preimage, which is where a reasoning step asks a ratio for its two
     * numbers and would spell them out to get an answer it takes a residue of.
     *
     * <p>The subject is the image and not the ratio: the type can hold a value compactly and still
     * lose it at the first step that asks the wrong question of it, and this is the step that asks.
     */
    @Test
    void aWideDecimalThroughAnImagesPreimageNeverSpellsItsPowersOut() {
        ExactRatio wide = TOO_WIDE_TO_SPELL;
        ExactRatio aThird = ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3));
        AdditiveImage overDecimals = new AdditiveImage.OverFiniteDecimals(wide);
        assertNotNull(overDecimals.affinePreimage(wide, wide, Granularity.DENSE));
        assertNotNull(overDecimals.affinePreimage(wide, wide, Granularity.DISCRETE));
        assertNotNull(overDecimals.affinePreimage(aThird, wide, Granularity.DENSE));
        assertNotNull(overDecimals.affinePreimage(aThird, wide, Granularity.DISCRETE));

        AdditiveImage overWhole = new AdditiveImage.OverWholeNumbers(wide);
        assertNotNull(overWhole.affinePreimage(wide, wide, Granularity.DENSE));
        assertNotNull(overWhole.affinePreimage(aThird, wide, Granularity.DENSE));
    }

    /**
     * The order answers every pair, including the ones the powers put far apart.
     *
     * <p>An order always exists, and {@link Comparable} says this one is total — so a pair it
     * declined would be a value this holds and cannot be reasoned about. The two here are decimals
     * written at either end of the scale a model may write, which is not a corner of the range:
     * embedding either of them is what this type exists to do.
     */
    @Test
    void theOrderAnswersEveryPairThePowersSetApart() {
        ExactRatio justOverOne = new ExactRatio(BigInteger.ONE, BigInteger.ONE,
                -69_657_842_846_620_870L, 30_000_000_000_000_000L);
        assertTrue(justOverOne.compareTo(ExactRatio.ONE) > 0);

        ExactRatio tiny = ExactRatio.of(new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE));
        ExactRatio huge = ExactRatio.of(new BigDecimal(BigInteger.ONE, Integer.MIN_VALUE));
        assertTrue(tiny.compareTo(huge) < 0);
        assertTrue(huge.compareTo(tiny) > 0);
        assertEquals(0, tiny.compareTo(ExactRatio.of(new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE))));

        ExactRatio wide = ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH);
        assertTrue(wide.compareTo(ExactRatio.ONE) < 0);
        assertTrue(wide.compareTo(ExactRatio.ZERO) > 0);
        assertTrue(wide.negated().compareTo(wide) < 0);
        assertEquals(0, wide.compareTo(ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH)));
    }

    /**
     * And the pairs a first reading cannot separate, which is the other arm.
     *
     * <p>Two values agreeing over thousands of bits are not told apart by a bracket of a hundred and
     * some, so the width goes up until they come apart — and that arm is reached by no pair a model
     * writes, which is exactly why it is asked for here. Each pair is put far apart by its powers as
     * well, so what separates them is the fraction and writing either of them out is not open.
     */
    @Test
    void theOrderTakesTheReadingAgainForAPairAFirstOneLeavesTogether() {
        ExactRatio far = new ExactRatio(BigInteger.ONE, BigInteger.ONE,
                -1_000_000_000L, -1_000_000_000L);
        for (int bits : new int[] {100, 400, 1600, 3200}) {
            ExactRatio aHair = new ExactRatio(BigInteger.ONE, BigInteger.ONE, -bits, 0);
            ExactRatio over = ExactRatio.ONE.plus(aHair);
            ExactRatio under = ExactRatio.ONE.minus(aHair);
            assertTrue(over.compareTo(ExactRatio.ONE) > 0, () -> "over one by a hair of " + bits);
            assertTrue(under.compareTo(ExactRatio.ONE) < 0, () -> "under one by a hair of " + bits);
            assertTrue(over.compareTo(under) > 0);
            assertTrue(over.negated().compareTo(ExactRatio.ONE.negated()) < 0);
            assertTrue(over.times(far).compareTo(far) > 0,
                    () -> "the same pair with its powers a billion apart, at " + bits);
        }
    }

    /**
     * Whether some decimal is this value, and whether one a carrier holds is, are two questions.
     *
     * <p>A scale is thirty-two bits, so a value that is a finite decimal can still be one nothing
     * writes — and a position holds what a model can write. Answering the second with the first
     * would let such a value into a coset of the decimals, which is a different set.
     */
    @Test
    void whatTerminatesAndWhatACarrierHoldsAreNotTheSameQuestion() {
        ExactRatio past = new ExactRatio(BigInteger.ONE, BigInteger.ONE,
                -3_000_000_000L, -3_000_000_000L);
        assertTrue(past.terminates(), "a millionth of a millionth of a millionth is a decimal");
        assertFalse(past.fitsWrittenDecimal(), "and no decimal here is written at that scale");
        assertThrows(ArithmeticException.class, past::asWrittenDecimal);

        assertTrue(TOO_WIDE_TO_SPELL.terminates());
        assertTrue(TOO_WIDE_TO_SPELL.fitsWrittenDecimal());

        ExactRatio aThird = ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3));
        assertFalse(aThird.terminates());
        assertFalse(aThird.fitsWrittenDecimal());
    }

    /**
     * The whole number a value stands above, for a value standing nowhere near one.
     *
     * <p>These exist for every value and are small for a small one, so working them out from the two
     * numbers refused a value over an answer that was never going to be large. The same reading the
     * order rests on answers them.
     */
    @Test
    void theWholeNumbersEitherSideOfATinyValueAreNotRefused() {
        ExactRatio tiny = ExactRatio.of(new BigDecimal(BigInteger.ONE, 2_000_000_000));
        assertEquals(BigInteger.ZERO, tiny.floor());
        assertEquals(BigInteger.ONE, tiny.ceiling());
        assertEquals(BigInteger.ZERO, tiny.truncated());
        assertEquals(BigInteger.valueOf(-1), tiny.negated().floor());
        assertEquals(BigInteger.ZERO, tiny.negated().ceiling());
        assertEquals(BigInteger.ZERO, tiny.negated().truncated());
        assertEquals(new BigDecimal("0.01"), tiny.asDecimal(java.math.RoundingMode.CEILING, 2));
        assertEquals(new BigDecimal("0.00"), tiny.asDecimal(java.math.RoundingMode.FLOOR, 2));
    }

    /**
     * The exponents are a range closed under negation, and that is asked where a ratio is made.
     *
     * <p>Every operation here turns an exponent round: a reciprocal negates both, reading the scale
     * of the decimal this is negates them, writing the powers out puts whichever is below the line
     * on the other side. The least number a long holds is its own negation, so a ratio standing at
     * it is one no operation could act on — and squaring a half reaches it, which is why this is a
     * rule and not a remark.
     */
    @Test
    void anExponentWhoseNegationIsNotHeldIsNotHeldEither() {
        assertThrows(ArithmeticException.class,
                () -> new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MIN_VALUE, 0));
        assertThrows(ArithmeticException.class,
                () -> new ExactRatio(BigInteger.ONE, BigInteger.ONE, 0, Long.MIN_VALUE));

        ExactRatio at = ExactRatio.of(BigInteger.ONE, BigInteger.TWO);
        for (int i = 0; i < 62; i++) {
            at = at.times(at);
        }
        assertEquals(-(1L << 62), at.twos());
        ExactRatio reached = at;
        assertThrows(ArithmeticException.class, () -> reached.times(reached));
    }

    /** The fraction is still there for a caller whose question is about those two numbers, and it is
     *  the fraction the value is rather than the pair the exponents were taken out of. */
    @Test
    void theFractionAskedForIsTheOneTheValueIs() {
        ExactRatio.Fraction twentieth =
                ExactRatio.of(new BigDecimal("0.05")).asFraction();
        assertEquals(BigInteger.ONE, twentieth.numerator());
        assertEquals(BigInteger.valueOf(20), twentieth.denominator());
        ExactRatio.Fraction whole = ExactRatio.of(new BigDecimal("300E-2")).asFraction();
        assertEquals(BigInteger.valueOf(3), whole.numerator());
        assertEquals(BigInteger.ONE, whole.denominator());
    }
}
