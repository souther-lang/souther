package souther.compiler.numeric;

import java.math.BigInteger;

/**
 * Where one {@link ExactRatio} stands against another, for the pairs their powers set far apart.
 *
 * <p>Cross-multiplying two of these writes out the difference between their exponents, and those run
 * to the width of a long — so a decimal written at one end of the scale a model may write, held
 * against one written at the other, asks for a number no machine builds. The order between them
 * exists all the same, and a type that is {@link Comparable} owes it.
 *
 * <p>So neither value is written out. Each magnitude is held between two whole numbers of a working
 * width times a power of two, every step rounding the two ends away from the value so that the
 * bracket holds by how it was built. Where the two brackets do not overlap the order is settled
 * exactly; where they do, the width rises and they are taken again. That ends, because one canonical
 * form per value means two records that are not equal are two magnitudes that are not equal, and two
 * unequal magnitudes stand some distance apart for a bracket to get inside of.
 *
 * <p><b>The same mathematics as the run time's {@code Rational} and deliberately not the same
 * code.</b> That type answers for the JVM and this package answers for what a declaration is, and
 * the second may not name the first (which {@code TheRuntimePackageIsTheBackendsToNameTest} holds).
 * What is carried over is the shape of the argument and not the type: a bracket per magnitude, a
 * power of five reached by squaring, and a width that rises until the pair comes apart. A third
 * caller for this would be the reason to find the two a shared home; two are not.
 */
final class ExactRatioOrder {

    /**
     * The width the first bracket is taken to, and the narrowest any reading here is taken at.
     *
     * <p>Wide enough that a second turn is rare, and small enough that the first is a few dozen
     * multiplications of numbers this size. Also wide enough to keep the two ends of a bracket a
     * long way apart in relative terms through a product and a reciprocal: taken narrow, the ends
     * spread until the lower one falls to nought, and a lower end of nought is a true statement
     * about the number that says nothing about one over it.
     */
    static final int FIRST_WIDTH = 128;

    private static final BigInteger FIVE = BigInteger.valueOf(5);

    private ExactRatioOrder() {
    }

    /**
     * Where {@code |a|} stands against {@code |b|}, both being non-zero.
     *
     * <p>Equal values are the caller's to answer, which it can do by the record's own equality: one
     * canonical form per value means that is the whole of it, and this would otherwise refine on a
     * pair no width ever separates.
     */
    static int compareMagnitudes(ExactRatio a, ExactRatio b) {
        for (int width = FIRST_WIDTH; ; width += width >> 1) {
            Integer decided = fromBrackets(a, b, width);
            if (decided != null) {
                return decided;
            }
        }
    }

    /** Which magnitude is the larger where brackets of {@code width} bits say so, and null where
     *  they overlap. */
    private static Integer fromBrackets(ExactRatio a, ExactRatio b, int width) {
        Bracketed here = magnitude(a, width);
        Bracketed there = magnitude(b, width);
        if (compareShifted(here.low, here.shift, there.high, there.shift) > 0) {
            return 1;
        }
        if (compareShifted(here.high, here.shift, there.low, there.shift) < 0) {
            return -1;
        }
        return null;
    }

    /**
     * One value's magnitude, held between two whole numbers of about {@code width} bits.
     *
     * <p>The fraction is bracketed by one division rather than kept whole, which is what holds every
     * number here to the working width: a numerator shifted to meet a denominator is the size of the
     * larger of the two, where a numerator multiplied by the other value's denominator is the size
     * of both together.
     *
     * <p>Reachable to a test, because what makes an order taken from brackets right is that each
     * bracket holds the value it was taken for — and a bracket that had slipped off the value by a
     * bit would answer nearly every pair the same way regardless. So the thing to put a question to
     * is this, and not the answers it goes on to give.
     */
    static Bracketed magnitude(ExactRatio of, int width) {
        Bracketed fraction = quotient(of.numeratorWithoutUnits().abs(),
                of.denominatorWithoutUnits(), width);
        long fives = of.fives();
        if (fives != 0) {
            Bracketed five = fiveTo(Math.abs(fives), width);
            fraction = fraction.times(fives > 0 ? five : five.reciprocal(width), width);
        }
        return fraction.shiftedBy(BigInteger.valueOf(of.twos()));
    }

    /**
     * {@code x / y} held between two whole numbers of about {@code width} bits.
     *
     * <p>Both sides are cut to the width first and what was cut off becomes part of the shift, so
     * nothing here is the size of either of them.
     */
    private static Bracketed quotient(BigInteger x, BigInteger y, int width) {
        Bracketed over = leadingBits(x, width);
        Bracketed under = leadingBits(y, width);
        return new Bracketed(
                over.low.shiftLeft(width).divide(under.high),
                over.high.shiftLeft(width).divide(under.low).add(BigInteger.ONE),
                over.shift.subtract(under.shift).subtract(BigInteger.valueOf(width)));
    }

    /** A whole number's leading bits: what was cut off is the shift, and the number stands between
     *  the bits that are left and one more of them. */
    private static Bracketed leadingBits(BigInteger whole, int width) {
        int over = whole.bitLength() - width;
        if (over <= 0) {
            return Bracketed.exactly(whole);
        }
        BigInteger kept = whole.shiftRight(over);
        return new Bracketed(kept, kept.add(BigInteger.ONE), BigInteger.valueOf(over));
    }

    /** {@code 5^exponent} bracketed to {@code width} bits, {@code exponent} being above nought.
     *  Reached by the bits of the exponent, so the work is their count and never the power itself. */
    private static Bracketed fiveTo(long exponent, int width) {
        Bracketed of = Bracketed.exactly(BigInteger.ONE);
        for (int bit = 63 - Long.numberOfLeadingZeros(exponent); bit >= 0; bit--) {
            of = of.squared(width);
            if ((exponent >>> bit & 1L) == 1L) {
                of = of.times(FIVE).keptTo(width);
            }
        }
        return of;
    }

    /**
     * Where {@code x × 2^a} stands against {@code y × 2^b}, both whole numbers being above nought.
     *
     * <p>Each side stands between its own count of bits and one more, so a gap of over one bit is
     * read off those counts and neither side is shifted — which is what keeps a shift no machine
     * holds out of this. Within a bit of one another, the two shifts are apart by no more than the
     * bits the two numbers hold, and the lesser side is lifted to meet the other.
     */
    private static int compareShifted(BigInteger x, BigInteger a, BigInteger y, BigInteger b) {
        BigInteger apart = a.add(BigInteger.valueOf(x.bitLength()))
                .subtract(b.add(BigInteger.valueOf(y.bitLength())));
        if (apart.compareTo(BigInteger.ONE) > 0) {
            return 1;
        }
        if (apart.negate().compareTo(BigInteger.ONE) > 0) {
            return -1;
        }
        BigInteger lift = a.subtract(b);
        return lift.signum() >= 0
                ? x.shiftLeft(lift.intValueExact()).compareTo(y)
                : x.compareTo(y.shiftLeft(lift.negate().intValueExact()));
    }

    /**
     * A number held between two whole numbers a count of bits short of it: the number is at least
     * {@code low × 2^shift} and at most {@code high × 2^shift}.
     *
     * <p>Every step rounds each end away from the number, so what a bracket says is true by how it
     * was built rather than by an error anyone has to have got right. What a width buys is how tight
     * the bracket is, never whether it holds.
     */
    record Bracketed(BigInteger low, BigInteger high, BigInteger shift) {

        static Bracketed exactly(BigInteger whole) {
            return new Bracketed(whole, whole, BigInteger.ZERO);
        }

        Bracketed times(BigInteger by) {
            return new Bracketed(low.multiply(by), high.multiply(by), shift);
        }

        /** The product of two brackets, which holds the product of any two numbers they hold — both
         *  standing above nought, so the ends multiply in the order they are in. */
        Bracketed times(Bracketed other, int width) {
            return new Bracketed(low.multiply(other.low), high.multiply(other.high),
                    shift.add(other.shift)).keptTo(width);
        }

        /**
         * One over this, bracketed to {@code width} bits.
         *
         * <p>The ends change places, the lower of the two coming from the upper of these. The
         * distance to shift by is a count of bits and is added as a long: added as an {@code int} it
         * would wrap where the width and a bit length together run past what one counts, and a shift
         * of a negative count is a shift the other way — which leaves a bracket with the value
         * outside it rather than a refusal, and that is an order answered wrongly.
         */
        Bracketed reciprocal(int width) {
            if (low.signum() <= 0) {
                throw new IllegalStateException(
                        "a bracket whose lower end has fallen to nought says nothing about one over"
                                + " the number it holds; the width it was taken to is too narrow to"
                                + " keep the two ends apart");
            }
            long by = (long) width + high.bitLength();
            if (by > Integer.MAX_VALUE) {
                throw new ArithmeticException("no whole number here is " + by + " bits");
            }
            BigInteger over = BigInteger.ONE.shiftLeft((int) by);
            return new Bracketed(over.divide(high), over.divide(low).add(BigInteger.ONE),
                    BigInteger.valueOf(-by).subtract(shift));
        }

        Bracketed shiftedBy(BigInteger bits) {
            return new Bracketed(low, high, shift.add(bits));
        }

        Bracketed squared(int width) {
            return new Bracketed(low.multiply(low), high.multiply(high), shift.add(shift))
                    .keptTo(width);
        }

        /** The same number, held between two numbers of no more than {@code width} bits. The lower
         *  end falls to where the shift leaves it and the upper end rises to the next one up, so the
         *  number stays inside. */
        Bracketed keptTo(int width) {
            int over = high.bitLength() - width;
            if (over <= 0) {
                return this;
            }
            BigInteger down = low.shiftRight(over);
            BigInteger up = high.shiftRight(over);
            if (up.shiftLeft(over).compareTo(high) < 0) {
                up = up.add(BigInteger.ONE);
            }
            return new Bracketed(down, up, shift.add(BigInteger.valueOf(over)));
        }
    }
}
