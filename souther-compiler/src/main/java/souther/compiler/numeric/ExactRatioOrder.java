package souther.compiler.numeric;

import java.math.BigInteger;

/**
 * Where one {@link ExactRatio} stands against another.
 *
 * <p>Cross-multiplying two of these writes out the difference between their exponents, and those run
 * to the width of a long — so a decimal written at one end of the scale a model may write, held
 * against one written at the other, asks for a number no machine builds. The order between them
 * exists all the same, and a type that is {@link Comparable} owes it.
 *
 * <p>There are two ways to it, and which answers is a matter of cost and never of what is answered.
 * Where the exponents of two and of five each differ by no more than {@link #NEAR_TWOS} and
 * {@link #NEAR_FIVES}, both values are written over one denominator and compared, which is a few
 * words of arithmetic ({@link #fromWritingBothOut}). Where they differ by more, or by more than a
 * difference of two exponents can hold, neither value is written out, and the rest of this is how.
 * {@code TwoRatiosAreOrderedAlikeWhereTheirPowersAreNearAndWhereTheyAreFarTest} holds the two to
 * one order on both sides of each edge.
 *
 * <p>Each magnitude is held between two whole numbers of a working
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
        Integer written = fromWritingBothOut(a, b);
        if (written != null) {
            return written;
        }
        for (int width = FIRST_WIDTH; ; width += width >> 1) {
            Integer decided = fromBrackets(a, b, width);
            if (decided != null) {
                return decided;
            }
        }
    }

    /** The most the two values' powers of two may stand apart for both to be written over one
     *  denominator, which is a shift of this many bits. */
    static final long NEAR_TWOS = 512;

    /** The same for five, which is a multiplication by a number of about two and a third times
     *  this many bits. */
    static final long NEAR_FIVES = 256;

    /**
     * Which magnitude is the larger, settled by writing both over one denominator, or null where
     * their powers stand too far apart for that to stay small.
     *
     * <p>Exact, and the same answer the brackets come to: what the brackets are for is the pair whose
     * powers no machine writes down. Most pairs are not that, and for those the difference between
     * the exponents is a shift and a small power of five, so the two products are a few words wide
     * and no width has to be tried.
     *
     * <p>Declined for a pair whose exponents cannot be subtracted without leaving what a long
     * holds, however small the difference would come out as: a difference that wrapped round is a
     * small number that says nothing about the pair.
     */
    static Integer fromWritingBothOut(ExactRatio a, ExactRatio b) {
        boolean subtractable = Math.abs(a.twos()) <= Integer.MAX_VALUE
                && Math.abs(b.twos()) <= Integer.MAX_VALUE
                && Math.abs(a.fives()) <= Integer.MAX_VALUE
                && Math.abs(b.fives()) <= Integer.MAX_VALUE;
        if (!subtractable) {
            return null;
        }
        long twos = a.twos() - b.twos();
        long fives = a.fives() - b.fives();
        if (Math.abs(twos) > NEAR_TWOS || Math.abs(fives) > NEAR_FIVES) {
            return null;
        }
        BigInteger left = a.numeratorWithoutUnits().abs().multiply(b.denominatorWithoutUnits());
        BigInteger right = b.numeratorWithoutUnits().abs().multiply(a.denominatorWithoutUnits());
        if (twos > 0) {
            left = left.shiftLeft((int) twos);
        } else if (twos < 0) {
            right = right.shiftLeft((int) -twos);
        }
        if (fives > 0) {
            left = left.multiply(FIVE.pow((int) fives));
        } else if (fives < 0) {
            right = right.multiply(FIVE.pow((int) -fives));
        }
        return left.compareTo(right);
    }

    /**
     * The whole number {@code |of|} stands above, {@code of} being neither nought nor a whole
     * number itself.
     *
     * <p>The same reading as the order and for the same reason. How large a value is and how large
     * the whole number below it is are not the same question: two powers that all but cancel leave a
     * value of about one and a whole number of one digit, and a step that worked the second out by
     * writing the value down refused it over an answer that was never going to be large. So the
     * brackets are taken and the width rises until both ends stand above the same whole number.
     *
     * <p>That ends because the value is not a whole number: two ends closing on a value strictly
     * inside a unit interval are inside it themselves once they stand closer together than the room
     * left either side. A whole number is where they would not, and is the caller's to answer — it
     * has the value already.
     */
    static BigInteger flooredMagnitude(ExactRatio of, BigInteger byTwos, BigInteger byFives) {
        for (int width = FIRST_WIDTH; ; width += width >> 1) {
            Bracketed held = magnitude(of, byTwos, byFives, width);
            BigInteger below = flooredEnd(held.low, held.shift);
            if (below.equals(flooredEnd(held.high, held.shift))) {
                return below;
            }
        }
    }

    /**
     * The whole number {@code end × 2^shift} stands above, the end being above nought.
     *
     * <p>A shift below nought by more than the end has bits leaves nothing above the point, and that
     * is read off the two counts rather than by shifting — the shifts a bracket of a value standing
     * near one carries are the size of the powers that value is written with, and no machine counts
     * those. Above nought the shift is the answer's own size, and where that is past what a whole
     * number here holds, so is the answer.
     */
    private static BigInteger flooredEnd(BigInteger end, BigInteger shift) {
        if (shift.signum() < 0) {
            return shift.negate().compareTo(BigInteger.valueOf(end.bitLength())) >= 0
                    ? BigInteger.ZERO
                    : end.shiftRight(shift.negate().intValueExact());
        }
        if (shift.add(BigInteger.valueOf(end.bitLength()))
                .compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) > 0) {
            throw new ArithmeticException(
                    "no whole number here is the one this value stands above");
        }
        return end.shiftLeft(shift.intValueExact());
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
     * <p><b>Taken at exponents given rather than at the value's own</b>, because a rounding asks
     * about this value times a power of ten and the tens it asks for are the caller's scale. Made
     * into a value of the ratio's own type first, that scale would have had to fit the exponents a
     * ratio holds — and a value whose powers all but cancel sits well inside them while either
     * exponent alone stands at the end. The answer was never out of reach; only a step on the way to
     * it would have been. So the exponents are whole numbers here and nothing is formed from them.
     *
     * <p>Reachable to a test, because what makes an order taken from brackets right is that each
     * bracket holds the value it was taken for — and a bracket that had slipped off the value by a
     * bit would answer nearly every pair the same way regardless. So the thing to put a question to
     * is this, and not the answers it goes on to give.
     */
    static Bracketed magnitude(ExactRatio of, BigInteger byTwos, BigInteger byFives, int width) {
        Bracketed fraction = quotient(of.numeratorWithoutUnits().abs(),
                of.denominatorWithoutUnits(), width);
        if (byFives.signum() != 0) {
            Bracketed five = fiveTo(byFives.abs(), width);
            fraction = fraction.times(
                    byFives.signum() > 0 ? five : five.reciprocal(width), width);
        }
        return fraction.shiftedBy(byTwos);
    }

    /** The same at the value's own exponents, which is what the order asks for. */
    static Bracketed magnitude(ExactRatio of, int width) {
        return magnitude(of, BigInteger.valueOf(of.twos()), BigInteger.valueOf(of.fives()), width);
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
    private static Bracketed fiveTo(BigInteger exponent, int width) {
        Bracketed of = Bracketed.exactly(BigInteger.ONE);
        for (int bit = exponent.bitLength() - 1; bit >= 0; bit--) {
            of = of.squared(width);
            if (exponent.testBit(bit)) {
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
