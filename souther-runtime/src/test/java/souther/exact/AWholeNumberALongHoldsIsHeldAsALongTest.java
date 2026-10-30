package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Each whole number of the parts is held as a long where a long holds it and wider where it does not,
 * and which follows from the number alone: parts handed over as {@code BigInteger}s and parts handed
 * over as longs are one representation of one value, so they are equal and hash alike — and hash as
 * they did when both numbers were {@code BigInteger}s, so no map keyed by a value is laid out anew.
 *
 * <p>Asked at the edges of a long: both signs of the largest magnitude, the least long, and the first
 * numbers past either end.
 */
class AWholeNumberALongHoldsIsHeldAsALongTest {

    private static final List<BigInteger> WHOLES = wholes();

    private static List<BigInteger> wholes() {
        List<BigInteger> out = new ArrayList<>();
        for (long each : new long[] {0, 1, 3, 16, 17, 1000, (1L << 31), (1L << 32) + 7,
                                     (1L << 62) - 1, (1L << 62), Long.MAX_VALUE}) {
            out.add(BigInteger.valueOf(each));
            out.add(BigInteger.valueOf(each).negate());
        }
        out.add(BigInteger.valueOf(Long.MIN_VALUE));
        out.add(BigInteger.valueOf(Long.MIN_VALUE).subtract(BigInteger.ONE));
        out.add(BigInteger.valueOf(Long.MAX_VALUE).add(BigInteger.ONE));
        out.add(BigInteger.ONE.shiftLeft(64).multiply(BigInteger.valueOf(15)));
        return out;
    }

    @Test
    void howTheNumbersAreHandedOverDoesNotChangeTheParts() {
        List<String> differ = new ArrayList<>();
        for (BigInteger numerator : WHOLES) {
            for (BigInteger denominator : WHOLES) {
                if (denominator.signum() == 0) {
                    continue;
                }
                ExactParts wide = new ExactParts(numerator, denominator, 3, -4);
                boolean inLongs = fits(numerator) && fits(denominator);
                if (wide.inLongs() != inLongs) {
                    differ.add(numerator + "/" + denominator + " held in longs: " + wide.inLongs());
                }
                if (!wide.numerator().equals(numerator) || !wide.denominator().equals(denominator)) {
                    differ.add(numerator + "/" + denominator + " read back as " + wide);
                }
                if (wide.hashCode() != hashOfTheNumbers(numerator, denominator, 3, -4)) {
                    differ.add(numerator + "/" + denominator + " hashes otherwise");
                }
                if (wide.signum() != numerator.signum()) {
                    differ.add(numerator + "/" + denominator + " has the sign " + wide.signum());
                }
                if (inLongs) {
                    ExactParts narrow = new ExactParts(numerator.longValueExact(),
                            denominator.longValueExact(), 3, -4);
                    if (!narrow.equals(wide) || narrow.hashCode() != wide.hashCode()) {
                        differ.add(numerator + "/" + denominator + " differs by how it came");
                    }
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    /** Two values that differ in one number are not equal, whichever way each number is held. */
    @Test
    void partsThatDifferInOneNumberAreNotEqual() {
        for (BigInteger one : WHOLES) {
            for (BigInteger other : WHOLES) {
                if (!one.equals(other)) {
                    assertNotEquals(new ExactParts(one, BigInteger.ONE, 0, 0),
                            new ExactParts(other, BigInteger.ONE, 0, 0), one + " against " + other);
                }
            }
        }
    }

    /** Parts already in canonical form are handed back as they are, so asking costs nothing new. */
    @Test
    void canonicalPartsAreHandedBackAsTheyAre() {
        ExactParts third = new ExactParts(1, 3, -2, 5);
        assertSame(third, ExactArithmetic.canonical(third));
        ExactParts unreduced = new ExactParts(-12, 30, 0, 0);
        assertEquals(new ExactParts(-1, 1, 1, -1), ExactArithmetic.canonical(unreduced));
        ExactParts belowTheLine = new ExactParts(1, -3, 0, 0);
        assertEquals(new ExactParts(-1, 3, 0, 0), ExactArithmetic.canonical(belowTheLine));
    }

    /** Asked of parts, the canonical form is the one asked of their numbers, at either width. */
    @Test
    void theCanonicalFormOfPartsIsTheOneOfTheirNumbers() {
        List<String> differ = new ArrayList<>();
        for (BigInteger numerator : WHOLES) {
            for (BigInteger denominator : WHOLES) {
                if (denominator.signum() == 0) {
                    continue;
                }
                ExactParts asked = ExactArithmetic.canonical(
                        new ExactParts(numerator, denominator, 3, -4));
                ExactParts expected = ExactArithmetic.canonical(numerator, denominator, 3, -4);
                if (!asked.equals(expected)) {
                    differ.add(numerator + "/" + denominator + ": " + asked + " != " + expected);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    private static boolean fits(BigInteger whole) {
        return whole.bitLength() < Long.SIZE;
    }

    /** The hash of the four numbers with both whole numbers as {@code BigInteger}s. */
    private static int hashOfTheNumbers(BigInteger numerator, BigInteger denominator, long twos,
                                        long fives) {
        int hash = numerator.hashCode();
        hash = 31 * hash + denominator.hashCode();
        hash = 31 * hash + Long.hashCode(twos);
        return 31 * hash + Long.hashCode(fives);
    }
}
