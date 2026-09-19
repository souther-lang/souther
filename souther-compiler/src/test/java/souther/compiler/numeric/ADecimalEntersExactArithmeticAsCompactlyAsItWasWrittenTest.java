package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.Duration;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
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

    @Test
    void theOrderOverACompactDecimalIsDecidedWithoutWritingItOut() {
        ExactRatio wide = ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH);
        assertTrue(wide.compareTo(ExactRatio.ONE) < 0);
        assertTrue(wide.compareTo(ExactRatio.ZERO) > 0);
        assertTrue(wide.negated().compareTo(wide) < 0);
        assertEquals(0, wide.compareTo(ExactRatio.of(A_MILLIONTH_OF_A_MILLIONTH)));
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
