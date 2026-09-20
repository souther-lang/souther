package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two ratios are put in the same order whether their powers stand near enough to be written out
 * over one denominator or too far apart for that.
 *
 * <p>The order has two ways to an answer. Where the exponents of two and of five differ by little,
 * both values are written over one denominator and compared; where they differ by more, each is
 * held between two whole numbers and the width rises until the two come apart. Either is exact, and
 * which of them answers is a matter of cost. So the answer must not move where the choice does, and
 * the pairs asked here stand on both sides of every edge the choice is made at, in each direction
 * and under every sign.
 *
 * <p>Held against the two values written out in full and cross-multiplied, which is what neither
 * way does: the near way takes the difference of the exponents first, and the far way never writes a
 * value out. The exponents here are small enough for that to be affordable, and it is the only
 * reading of the order that shares nothing with either.
 *
 * <p>The edges are read from the constants the choice is made by, so moving them moves what is
 * asked. {@link #theNearWayIsTakenExactlyWhereItsEdgesSayAndBothSidesAreAsked} is what says that
 * both ways are reached and not one of them by default.
 */
class TwoRatiosAreOrderedAlikeWhereTheirPowersAreNearAndWhereTheyAreFarTest {

    private static final BigInteger FIVE = BigInteger.valueOf(5);

    /** Numerators and denominators with neither a factor of two nor of five in them, so the
     *  exponents below are the ones the value stands at and not ones the constructor moves. Signs
     *  are on the numerator. */
    private static final long[][] SHAPES = {
            {1, 1}, {3, 7}, {9, 11}, {13, 3}, {-3, 7}, {-1, 3}, {101, 99}, {-7, 9}};

    /** How far apart the powers of two of a pair stand: on each side of the edge and of nought. */
    private static final long[] TWOS_APART = around(ExactRatioOrder.NEAR_TWOS);

    /** The same for five. */
    private static final long[] FIVES_APART = around(ExactRatioOrder.NEAR_FIVES);

    /** Where the first of a pair stands, so that only the differences are what is asked and not
     *  where the exponents happen to be centred. */
    private static final long[][] STARTING_AT = {{0, 0}, {-300, 150}, {300, -150}};

    private static long[] around(long edge) {
        long[] out = {0, 1, edge - 1, edge, edge + 1, 2 * edge};
        long[] both = new long[2 * out.length - 1];
        for (int at = 0; at < out.length; at++) {
            both[at] = out[at];
            if (at > 0) {
                both[out.length - 1 + at] = -out[at];
            }
        }
        return both;
    }

    private record Pair(ExactRatio a, ExactRatio b, long twosApart, long fivesApart) {
        @Override
        public String toString() {
            return a + " against " + b + ", " + twosApart + " apart in twos and " + fivesApart
                    + " in fives";
        }
    }

    private static List<Pair> everyPair() {
        List<Pair> out = new ArrayList<>();
        for (long[] start : STARTING_AT) {
            for (long twos : TWOS_APART) {
                for (long fives : FIVES_APART) {
                    for (long[] first : SHAPES) {
                        for (long[] second : SHAPES) {
                            out.add(new Pair(
                                    ratio(first, start[0], start[1]),
                                    ratio(second, start[0] - twos, start[1] - fives),
                                    twos, fives));
                        }
                    }
                }
            }
        }
        return out;
    }

    private static ExactRatio ratio(long[] shape, long twos, long fives) {
        return new ExactRatio(BigInteger.valueOf(shape[0]), BigInteger.valueOf(shape[1]), twos,
                fives);
    }

    /** {@code |of|} written out in full, as a numerator and a denominator. */
    private static BigInteger[] writtenOut(ExactRatio of) {
        BigInteger numerator = of.numeratorWithoutUnits().abs();
        BigInteger denominator = of.denominatorWithoutUnits();
        if (of.twos() >= 0) {
            numerator = numerator.shiftLeft((int) of.twos());
        } else {
            denominator = denominator.shiftLeft((int) -of.twos());
        }
        if (of.fives() >= 0) {
            numerator = numerator.multiply(FIVE.pow((int) of.fives()));
        } else {
            denominator = denominator.multiply(FIVE.pow((int) -of.fives()));
        }
        return new BigInteger[] {numerator, denominator};
    }

    /** Where {@code |a|} stands against {@code |b|}, by cross-multiplying what is written out. */
    private static int byWritingBothOut(ExactRatio a, ExactRatio b) {
        BigInteger[] left = writtenOut(a);
        BigInteger[] right = writtenOut(b);
        return left[0].multiply(right[1]).compareTo(right[0].multiply(left[1]));
    }

    /** Where {@code a} stands against {@code b} with the signs they carry. */
    private static int signedByWritingBothOut(ExactRatio a, ExactRatio b) {
        BigInteger[] left = writtenOut(a);
        BigInteger[] right = writtenOut(b);
        return left[0].multiply(BigInteger.valueOf(a.numeratorWithoutUnits().signum()))
                .multiply(right[1])
                .compareTo(right[0].multiply(BigInteger.valueOf(b.numeratorWithoutUnits().signum()))
                        .multiply(left[1]));
    }

    @Test
    void everyPairIsOrderedAsWritingBothOutOrdersIt() {
        int asked = 0;
        for (Pair each : everyPair()) {
            int expected = Integer.signum(byWritingBothOut(each.a(), each.b()));
            if (expected == 0) {
                continue;
            }
            asked++;
            assertEquals(expected, Integer.signum(ExactRatioOrder.compareMagnitudes(each.a(),
                    each.b())), () -> "the larger of " + each);
            assertEquals(-expected, Integer.signum(ExactRatioOrder.compareMagnitudes(each.b(),
                    each.a())), () -> "the larger of " + each + ", asked the other way round");
        }
        assertTrue(asked > 1000, "the pairs asked are a population and not a handful: " + asked);
    }

    @Test
    void theSignsALargerOrSmallerValueCarriesAreTakenOnTopOfTheMagnitude() {
        for (Pair each : everyPair()) {
            assertEquals(Integer.signum(signedByWritingBothOut(each.a(), each.b())),
                    Integer.signum(each.a().compareTo(each.b())), () -> "the order of " + each);
        }
    }

    /**
     * Exponents too large to be subtracted are left to the brackets, however they stand.
     *
     * <p>The difference of two exponents is what the near way is decided by, and the difference of
     * two longs at opposite ends is not a long. A pair like that read as near would be answered from
     * a wrapped-round number; asked here at exponents past an int, and at ones that overflow when
     * one is taken from the other, of two values that differ by nothing else, so that the one with
     * the larger exponent is the larger without a word about how it is worked out.
     */
    @Test
    void exponentsTooLargeToSubtractAreLeftToTheBracketsAndStillOrdered() {
        long[] beyondAnInt = {1L << 31, -(1L << 31), 1L << 40, -(1L << 40), 1L << 62, -(1L << 62)};
        for (long high : beyondAnInt) {
            for (long low : beyondAnInt) {
                if (high <= low) {
                    continue;
                }
                ExactRatio larger = ratio(new long[] {3, 7}, high, 0);
                ExactRatio smaller = ratio(new long[] {3, 7}, low, 0);
                assertEquals(1, Integer.signum(ExactRatioOrder.compareMagnitudes(larger, smaller)),
                        () -> "2^" + high + " against 2^" + low);
                assertEquals(-1, Integer.signum(ExactRatioOrder.compareMagnitudes(smaller, larger)),
                        () -> "2^" + low + " against 2^" + high);
                ExactRatio largerFives = ratio(new long[] {3, 7}, 0, high);
                ExactRatio smallerFives = ratio(new long[] {3, 7}, 0, low);
                assertEquals(1, Integer.signum(
                        ExactRatioOrder.compareMagnitudes(largerFives, smallerFives)),
                        () -> "5^" + high + " against 5^" + low);
            }
        }
    }

    /**
     * Both ways are reached, and each where the constants say.
     *
     * <p>The population above stands on both sides of each edge, but a pair only says something
     * about the near way if the near way was the one to answer it. So the way taken is read here:
     * the near way answers a pair exactly where neither exponent stands further apart than its
     * edge, and declines every other, which the far way then answers.
     */
    @Test
    void theNearWayIsTakenExactlyWhereItsEdgesSayAndBothSidesAreAsked() {
        int near = 0;
        int far = 0;
        for (Pair each : everyPair()) {
            boolean withinEdges = Math.abs(each.twosApart()) <= ExactRatioOrder.NEAR_TWOS
                    && Math.abs(each.fivesApart()) <= ExactRatioOrder.NEAR_FIVES;
            boolean taken = ExactRatioOrder.fromWritingBothOut(each.a(), each.b()) != null;
            assertEquals(withinEdges, taken, () -> "which way answers " + each);
            if (taken) {
                near++;
            } else {
                far++;
            }
        }
        assertTrue(near > 0, "no pair was answered by writing both out");
        assertTrue(far > 0, "no pair was left to the brackets");
    }
}
