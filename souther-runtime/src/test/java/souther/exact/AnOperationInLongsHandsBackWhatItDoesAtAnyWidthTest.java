package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.function.BinaryOperator;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A sum, a product and a quotient worked out in longs are the parts the same operation hands back
 * at any width, and where the long route does not hold the working, the operation is the one at any
 * width — its answer, or its refusal and the words of it.
 *
 * <p>Asked over every pair of operands drawn from values at the edges as well as ordinary ones:
 * both signs, the largest magnitudes the long route takes and the smallest it does not, numbers past
 * sixty-four bits, denominators a sum multiplies past a long while the sum is an ordinary value,
 * and exponents at both ends of a long, where the answer has no representation. The operands are
 * not all canonical, because a sum of many terms hands one sum on to the next without making it so.
 */
class AnOperationInLongsHandsBackWhatItDoesAtAnyWidthTest {

    private static final List<ExactParts> OPERANDS = operands();

    @Test
    void aSumIsWhatItIsAtAnyWidth() {
        assertEquals(List.of(), differences(ExactArithmetic::plus, ExactArithmetic::plusInLongs,
                ExactArithmetic::plusAtAnyWidth));
    }

    @Test
    void aProductIsWhatItIsAtAnyWidth() {
        assertEquals(List.of(), differences(ExactArithmetic::times, ExactArithmetic::timesInLongs,
                ExactArithmetic::timesAtAnyWidth));
    }

    @Test
    void aQuotientIsWhatItIsAtAnyWidth() {
        assertEquals(List.of(), differences(ExactArithmetic::dividedBy,
                ExactArithmetic::dividedByInLongs, ExactArithmetic::dividedByAtAnyWidth));
    }

    /** The long route is taken where it holds, which the answers alone would not show: every one of
     *  these is the same whichever way it was worked out. */
    @Test
    void smallOperandsAreWorkedOutInLongs() {
        ExactParts third = parts(1, 3, 0, 0);
        ExactParts sixth = parts(1, 3, -1, 0);
        ExactParts tenth = parts(-1, 1, -1, -1);

        assertEquals(parts(3, 3, -1, 0), ExactArithmetic.plusInLongs(third, sixth),
                "a third and a sixth over a common denominator, the half not yet taken out of it");
        assertNotNull(ExactArithmetic.plusInLongs(third, tenth));
        assertEquals(parts(1, 9, -1, 0), ExactArithmetic.timesInLongs(third, sixth));
        assertEquals(parts(-1, 1, -1, -1), ExactArithmetic.dividedByInLongs(tenth, parts(1, 1, 0, 0)));
        assertEquals(parts(1, -3, 1, 1), ExactArithmetic.dividedByInLongs(third, tenth),
                "a negative divisor's sign stays below the line");
    }

    /** And not where the working is past a long, though the answer is an ordinary value. */
    @Test
    void aSumWhoseDenominatorsMultiplyPastALongIsFormedAtAnyWidth() {
        long power = 1L << 40;
        ExactParts one = parts(1, power + 3, 0, 0);
        ExactParts other = parts(-1, power + 5, 0, 0);

        assertNull(ExactArithmetic.plusInLongs(one, other));
        ExactParts sum = ExactArithmetic.plus(one, other);
        assertEquals(BigInteger.valueOf(power + 3).multiply(BigInteger.valueOf(power + 5)),
                sum.denominator());
        assertEquals(BigInteger.TWO, sum.numerator());
    }

    /** Two magnitudes ordered in longs stand as the order at any width stands them; a caller counting
     *  the brackets is handed the order at any width, so the long route is asked for here directly. */
    @Test
    void anOrderIsWhatItIsAtAnyWidth() {
        List<String> differ = new ArrayList<>();
        int takenInLongs = 0;
        int goneWide = 0;
        for (ExactParts a : nearOperands()) {
            for (ExactParts b : nearOperands()) {
                if (a.isZero() || b.isZero()) {
                    continue;
                }
                int narrow = ExactArithmetic.magnitudesInLongs(a, b);
                if (narrow == ExactArithmetic.UNDECIDED) {
                    goneWide++;
                    continue;
                }
                takenInLongs++;
                int wide = ExactOrder.magnitudes(a, b);
                if (narrow != wide) {
                    differ.add(a + " against " + b + ": " + narrow + " != " + wide);
                }
            }
        }
        if (takenInLongs == 0 || goneWide == 0) {
            differ.add("in longs " + takenInLongs + ", at any width " + goneWide);
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    /** A value rounded to a scale in longs is the whole number the rounding at any width comes to, at
     *  every policy, and refused as it refuses where no rounding was named. */
    @Test
    void aRoundingIsWhatItIsAtAnyWidth() {
        List<String> differ = new ArrayList<>();
        int takenInLongs = 0;
        int goneWide = 0;
        for (ExactParts of : nearOperands()) {
            for (int scale : new int[] {-20, -3, -1, 0, 1, 2, 5, 30}) {
                for (RoundingMode towards : RoundingMode.values()) {
                    String narrow = outcome(() -> ExactRounding.roundedInLongs(of, scale, towards));
                    if (narrow.equals("null")) {
                        goneWide++;
                        continue;
                    }
                    takenInLongs++;
                    String wide = outcome(() -> ExactRounding.roundedTimesTenTo(of, scale, towards,
                            _ -> { }));
                    if (!narrow.equals(wide)) {
                        differ.add(of + " at " + scale + " " + towards + ": " + narrow + " != " + wide);
                    }
                }
            }
        }
        if (takenInLongs == 0 || goneWide == 0) {
            differ.add("in longs " + takenInLongs + ", at any width " + goneWide);
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    /** The operands in canonical form, which is what the order and the rounding are handed, whose
     *  exponents stand within a few dozen of nought — which the two settle at any width without
     *  refining far. */
    private static List<ExactParts> nearOperands() {
        List<ExactParts> out = new ArrayList<>();
        for (ExactParts each : OPERANDS) {
            if (each.twos() > -64 && each.twos() < 64 && each.fives() > -64 && each.fives() < 64) {
                out.add(ExactArithmetic.canonical(each));
            }
        }
        return out;
    }

    private static String outcome(Supplier<Object> asked) {
        try {
            return String.valueOf(asked.get());
        } catch (RuntimeException refused) {
            return refused.getClass().getSimpleName() + ": " + refused.getMessage();
        }
    }

    /** Which is why neither route asks after one: no parts have a nought below the line. */
    @Test
    void noPartsHaveANoughtBelowTheLine() {
        assertThrows(IllegalArgumentException.class,
                () -> new ExactParts(BigInteger.valueOf(3), BigInteger.ZERO, 0, 0));
    }

    private static List<String> differences(BinaryOperator<ExactParts> operation,
                                            BinaryOperator<ExactParts> inLongs,
                                            BinaryOperator<ExactParts> atAnyWidth) {
        List<String> differ = new ArrayList<>();
        int takenInLongs = 0;
        int goneWide = 0;
        for (ExactParts a : OPERANDS) {
            for (ExactParts b : OPERANDS) {
                String asked = outcome(operation, a, b);
                String wide = outcome(atAnyWidth, a, b);
                if (!asked.equals(wide)) {
                    differ.add(a + " and " + b + ": " + asked + " != " + wide);
                }
                String narrow = outcome(inLongs, a, b);
                if (narrow.equals("null")) {
                    goneWide++;
                } else {
                    takenInLongs++;
                    if (!narrow.equals(wide)) {
                        differ.add(a + " and " + b + " in longs: " + narrow + " != " + wide);
                    }
                }
            }
        }
        // Both routes, or the comparison is of one of them with itself.
        if (takenInLongs == 0 || goneWide == 0) {
            differ.add("in longs " + takenInLongs + ", at any width " + goneWide);
        }
        return differ.subList(0, Math.min(differ.size(), 5));
    }

    /** What an operation answers, or which failure it refuses with and in what words. */
    private static String outcome(BinaryOperator<ExactParts> operation, ExactParts a, ExactParts b) {
        try {
            return String.valueOf(operation.apply(a, b));
        } catch (RuntimeException refused) {
            return refused.getClass().getSimpleName() + ": " + refused.getMessage();
        }
    }

    private static List<ExactParts> operands() {
        List<BigInteger> wholes = new ArrayList<>();
        for (long each : new long[] {1, 2, 3, 5, 6, 7, 10, 25, 125, 1024, 3125, 999_999_937L,
                                     (1L << 40) + 3, (1L << 40) + 5, (1L << 61) - 1, (1L << 61),
                                     (1L << 62) - 1, (1L << 62), Long.MAX_VALUE}) {
            wholes.add(BigInteger.valueOf(each));
        }
        wholes.add(BigInteger.ONE.shiftLeft(64).add(BigInteger.valueOf(7)));
        long[] exponents = {0, 1, -1, 3, -7, 26, 27, -27, 40, 62, 63, Long.MAX_VALUE,
                            Long.MAX_VALUE - 1, Long.MIN_VALUE, Long.MIN_VALUE + 1};
        List<ExactParts> out = new ArrayList<>();
        out.add(ExactParts.ZERO);
        Random random = new Random(20261017L);
        for (int i = 0; i < 100; i++) {
            BigInteger numerator = wholes.get(random.nextInt(wholes.size()));
            BigInteger denominator = random.nextInt(3) == 0 ? BigInteger.ONE
                    : wholes.get(random.nextInt(wholes.size()));
            if (random.nextBoolean()) {
                numerator = numerator.negate();
            }
            if (random.nextInt(8) == 0) {
                denominator = denominator.negate();
            }
            long twos = random.nextInt(3) == 0 ? exponents[random.nextInt(exponents.length)]
                    : random.nextInt(9) - 4;
            long fives = random.nextInt(3) == 0 ? exponents[random.nextInt(exponents.length)]
                    : random.nextInt(9) - 4;
            out.add(new ExactParts(numerator, denominator, twos, fives));
        }
        return out;
    }

    private static ExactParts parts(long numerator, long denominator, long twos, long fives) {
        return new ExactParts(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator), twos,
                fives);
    }
}
