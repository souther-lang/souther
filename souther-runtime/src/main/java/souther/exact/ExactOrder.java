package souther.exact;

import org.jspecify.annotations.Nullable;

import java.math.BigInteger;
import java.util.function.Supplier;

import static souther.exact.ExactPowers.FIVE;

/**
 * Where one exact rational stands against another, and the brackets that read a value without
 * building the powers it stands for.
 *
 * <p>Answered for every pair, and answered without building a power for all but the pairs where
 * building one is the cheaper way. What a value is made of beyond its stored fraction is a power of
 * two, which is a count of bits, and a power of five, which is bracketed between two whole numbers of a
 * working width by squaring — so the work is the bits of an exponent rather than its size.
 *
 * <p>An order always exists, so it rests on neither of the two things that would refuse it: not on a
 * precision settled before the pair arrived, two fractions being able to stand closer than any such
 * precision; and not on the powers the two values stand for, the pairs whose logs sit closest together
 * being the ones whose powers are largest. Telling two values apart takes as many bits as they agree
 * over, so a comparison may want working room in proportion to what it was handed. Where that room is
 * not to be had the run has failed and says so ({@link ExactRoomExceeded}), and a platform that
 * supplies what the decision wanted answers the same pair.
 *
 * <p>Three bounds stand behind everything here, and they are not the same kind of thing. The
 * exponent's width is the arithmetic's own, and a value past it has no representation. The platform's
 * largest whole number is the room this runs in. A bracket's width is neither: it is an instrument, and
 * an instrument too coarse for a question is a reason to take a finer one and never a reason to refuse.
 */
final class ExactOrder {

    /**
     * How many bits a power of five is first bracketed to when a comparison asks for one.
     *
     * <p>A starting point and not a limit: a bracket too wide to separate the pair it was taken for is
     * taken again wider ({@link WidthsToTry}). Wide enough that the second turn is not reached by any
     * pair a comparison is likely to be asked about, and small enough that the first turn is a few dozen
     * multiplications of numbers this size.
     */
    static final int BRACKET_BITS = 128;

    /**
     * How many times over what a pair already takes up a cheap exact writing of it may form.
     *
     * <p>A cost policy and nothing else — every value it turns away is answered by the reading below it.
     * Over the two and a third bits a factor of five takes, so that a pair whose exponents nearly cancel
     * is written out rather than refined, and small enough that a pair brought close by exponents too
     * large to write down is refined rather than written.
     */
    private static final int A_FEW_TIMES = 4;

    /** More bits than a factor of five takes, which is over two and a third of them. Counted over the
     *  truth so that the count of what a writing would cost is over it too. */
    private static final int MORE_BITS_THAN_A_FIVE_TAKES = 3;

    private ExactOrder() {
    }

    /**
     * Where {@code |a|} stands against {@code |b|}, both being non-zero and unequal.
     *
     * <p>Unequal is what makes the refinement end. Two canonical values of one magnitude and one sign
     * are equal records, and the caller answered those before reaching here.
     */
    static int magnitudes(ExactParts a, ExactParts b) {
        return magnitudeWithAWritingWorth(a, b, bitsAWritingIsWorth(storedBits(a) + storedBits(b)));
    }

    /**
     * Four readings, and only the last one always answers.
     *
     * <p>The three above it are there because they are cheap, and each is allowed to decline: a bracket
     * of the starting width settles nearly every pair for a few dozen multiplications of small numbers;
     * writing both values out as one fraction each settles a pair whose powers are worth writing down;
     * and the same writing with the exponents' difference on one side settles a pair whose huge exponents
     * cancel. What is left over goes to the refinement, which asks for no width in advance and so has
     * nothing to decline for.
     *
     * <p>Apart from {@link #magnitudes} so that the readings can be asked for as a sequence, with what a
     * writing may cost stated rather than worked out.
     */
    static int magnitudeWithAWritingWorth(ExactParts a, ExactParts b, long bitsAWritingMayForm) {
        Integer quickly = magnitudeFromBrackets(a, b, BRACKET_BITS);
        if (quickly != null) {
            return quickly;
        }
        Integer exactly = magnitudeWrittenOut(a, b, bitsAWritingMayForm);
        if (exactly != null) {
            return exactly;
        }
        // Asked the other way about, which is a different pair of fractions to write out and so a
        // different question about cost. Where one side's powers cancel the other's, only one of the two
        // writings is worth taking, and which of them that is has nothing to do with which value was
        // asked about — so an order that took one writing and stopped would read one pair two ways.
        Integer theOtherWayAbout = magnitudeWrittenOut(b, a, bitsAWritingMayForm);
        if (theOtherWayAbout != null) {
            return -theOtherWayAbout;
        }
        return magnitudeByRefining(a, b);
    }

    /** How many bits the parts a value stores take up, which is what holding it costs. */
    static long storedBits(ExactParts of) {
        return (long) of.numerator().abs().bitLength() + of.denominator().bitLength();
    }

    /**
     * How large a whole number a writing may form before the refinement is the cheaper way to the
     * answer, for values whose stored parts take up this many bits.
     *
     * <p>A cost and nothing else: what the readings above the refinement are for is being cheap, so what
     * they decide is not whether the host could hold the number but whether the number is worth forming.
     * A multiple of what the values already take up, because that is what the refinement costs — two
     * values whose stored fractions are of some size cannot agree over much more than that size unless
     * their exponents very nearly cancel, in which case what the writing forms is of that size too.
     * Declining where the writing would have done is free, since it sends the pair to a reading that
     * answers.
     */
    static long bitsAWritingIsWorth(long stored) {
        return A_FEW_TIMES * stored + BRACKET_BITS;
    }

    /**
     * Where {@code |a|} stands against {@code |b|}, from brackets taken again wider until they come
     * apart.
     *
     * <p>This holds nothing back: a bracket holds the value it was taken for by how it was built, so a
     * pair the brackets separate is separated exactly, and two unequal magnitudes stand some distance
     * apart for a bracket to get inside of. The only way this does not answer is the host running out of
     * room to hold the next width, which is the run failing and not a pair declined.
     *
     * <p>Apart from {@link #magnitudes} so that a test can ask this rung the pairs the ones above it
     * would have answered.
     */
    static int magnitudeByRefining(ExactParts a, ExactParts b) {
        return asWideAsItTakes(
                width -> magnitudeFromBrackets(a, b, width),
                () -> "tell two values apart");
    }

    /** A question a bracket of some width either settles or leaves open. */
    interface ReadFromABracket<T> {
        @Nullable T atAWidthOf(int bits);
    }

    /**
     * The first answer a reading gives as the width rises, and the run's shortage where no width this
     * run holds gives one.
     *
     * <p>One mechanism for the order and for the rounding, which ask the same thing of a bracket: both
     * are a question with finitely many answers whose subject is an exact value, so both are settled by
     * any bracket tight enough and by no width known before the value arrives.
     *
     * <p>The run's shortage at one width is caught, and no other thing is. A width the host has no room
     * for says nothing about the widths below it, so what is finished is the rising, and what follows is
     * the search for the widest width there is room for. A failure of the answer itself passes through
     * untouched, and so does an error of the host's own.
     */
    static <T> T asWideAsItTakes(ReadFromABracket<T> reading, Supplier<String> theQuestion) {
        WidthsToTry widths = WidthsToTry.aboveAWidthOf(BRACKET_BITS);
        while (widths.thereIsOneToTry()) {
            int width = widths.next();
            T decided;
            try {
                decided = reading.atAWidthOf(width);
            } catch (ExactRoomExceeded _) {
                widths = widths.wasTooWide(width);
                continue;
            }
            if (decided != null) {
                return decided;
            }
            widths = widths.wasNotWideEnough(width);
        }
        throw new ExactRoomExceeded("no room to " + theQuestion.get());
    }

    /**
     * The widths a reading is taken at: which to try next, given the widest one known to be held and the
     * narrowest one known to be past what the host holds.
     *
     * <p>Two searches are going on and the reading is the subject of neither. One is for the precision
     * the question needs, which rises; the other is for where the host's room gives out, which is found
     * only by asking. So the rise stops at the first failure and the search turns inward: between a
     * width that was held and one that was not, it tries the middle, and either side tells it which half
     * to keep. That ends, having tried a width the host holds and within a bit of the widest there is.
     * Only then is the room genuinely out.
     *
     * <p>Half again each turn while it rises, and never by fewer than a few dozen bits. The widest width
     * the host counts is tried rather than stepped over.
     */
    private record WidthsToTry(int held, int past) {

        private static final int A_FEW_DOZEN_BITS = 64;

        /** No width is known to be past what the host holds until one has failed, and nought is no width. */
        private static final int NONE_HAS_FAILED = 0;

        static WidthsToTry aboveAWidthOf(int held) {
            return new WidthsToTry(held, NONE_HAS_FAILED);
        }

        boolean thereIsOneToTry() {
            return past == NONE_HAS_FAILED ? held < Integer.MAX_VALUE : past - held > 1;
        }

        int next() {
            if (past == NONE_HAS_FAILED) {
                return (int) Math.min(
                        held + Math.max(A_FEW_DOZEN_BITS, held / 2L), Integer.MAX_VALUE);
            }
            return held + (past - held) / 2;
        }

        WidthsToTry wasNotWideEnough(int width) {
            return new WidthsToTry(width, past);
        }

        WidthsToTry wasTooWide(int width) {
            return new WidthsToTry(held, width);
        }
    }

    /**
     * Where {@code |a|} stands against {@code |b|} by writing both out as one fraction each, and null
     * where what that takes altogether is not worth forming.
     *
     * <p>Each value is written out at its own exponents first, which is the writing that does not depend
     * on which of the two was asked about. Where that is not worth it, the difference of the two
     * exponents is put on the first side instead and the other side is left as it stands: two values of
     * huge but equal exponents cancel that way and are written out where their own forms would have cost
     * too much.
     *
     * <p>A writing is what its numbers come to together, because they are all held at once and it is what
     * the reading costs that is being weighed.
     */
    static @Nullable Integer magnitudeWrittenOut(ExactParts a, ExactParts b, long within) {
        BigInteger @Nullable [] eachAtItsOwn = allWrittenOut(within,
                new ToWriteOut(a.numerator().abs(),
                        BigInteger.valueOf(a.twos()), BigInteger.valueOf(a.fives())),
                new ToWriteOut(a.denominator(),
                        BigInteger.valueOf(a.twos()).negate(), BigInteger.valueOf(a.fives()).negate()),
                new ToWriteOut(b.numerator().abs(),
                        BigInteger.valueOf(b.twos()), BigInteger.valueOf(b.fives())),
                new ToWriteOut(b.denominator(),
                        BigInteger.valueOf(b.twos()).negate(), BigInteger.valueOf(b.fives()).negate()));
        if (eachAtItsOwn != null) {
            return comparedAsFractions(
                    eachAtItsOwn[0], eachAtItsOwn[1], eachAtItsOwn[2], eachAtItsOwn[3]);
        }
        BigInteger byTwos = apart(a.twos(), b.twos());
        BigInteger byFives = apart(a.fives(), b.fives());
        BigInteger @Nullable [] theDifferenceOnThisSide = allWrittenOut(within,
                new ToWriteOut(a.numerator().abs(), byTwos, byFives),
                new ToWriteOut(a.denominator(), byTwos.negate(), byFives.negate()));
        return theDifferenceOnThisSide == null ? null
                : comparedAsFractions(theDifferenceOnThisSide[0], theDifferenceOnThisSide[1],
                        b.numerator().abs(), b.denominator());
    }

    /** A whole number to be written out with powers in it: what the powers multiply, and the powers. A
     *  negative one of them belongs to the other side of the fraction and counts for nothing here. */
    record ToWriteOut(BigInteger whole, BigInteger twos, BigInteger fives) {

        /** How many bits writing it out takes, counted over the truth so that a writing is turned away
         *  rather than attempted where the count is the wrong side of the budget. */
        BigInteger bits() {
            return BigInteger.valueOf(whole.bitLength())
                    .add(twos.max(BigInteger.ZERO))
                    .add(fives.max(BigInteger.ZERO)
                            .multiply(BigInteger.valueOf(MORE_BITS_THAN_A_FIVE_TAKES)));
        }

        @Nullable BigInteger written() {
            return writtenOut(whole, twos, fives);
        }
    }

    /** All of them written out, or null where what they come to together is past {@code within} bits or
     *  where the host turns one of them down after all. */
    static BigInteger @Nullable [] allWrittenOut(long within, ToWriteOut... these) {
        BigInteger bits = BigInteger.ZERO;
        for (ToWriteOut one : these) {
            bits = bits.add(one.bits());
        }
        if (bits.compareTo(BigInteger.valueOf(within)) > 0) {
            return null;
        }
        BigInteger[] written = new BigInteger[these.length];
        for (int at = 0; at < these.length; at++) {
            BigInteger one = these[at].written();
            if (one == null) {
                return null;
            }
            written[at] = one;
        }
        return written;
    }

    /** How far one exponent stands from another, held wider than an exponent is — the difference of two
     *  of them is not bounded by what one of them holds. */
    private static BigInteger apart(long exponent, long from) {
        return BigInteger.valueOf(exponent).subtract(BigInteger.valueOf(from));
    }

    /**
     * A whole number written out with those powers in it, or null where the host turns it down.
     *
     * <p>What it would cost is counted before this is reached, by whoever is weighing the whole writing,
     * and counted over the truth, so a writing that would have fitted its budget is sometimes turned
     * away. That is the side to be wrong on: a writing turned away costs nothing and the pair is answered
     * by the refinement, while a writing attempted at hundreds of megabytes costs that whether or not it
     * ends in a number. The host's own refusal is still caught, a budget being a cost and not a promise
     * about what fits.
     */
    private static @Nullable BigInteger writtenOut(
            BigInteger whole, BigInteger twos, BigInteger fives) {
        try {
            return ExactPowers.built(whole, twos.max(BigInteger.ZERO), fives.max(BigInteger.ZERO));
        } catch (ArithmeticException _) {
            return null;
        }
    }

    /**
     * Where {@code |a|} stands against {@code |b|} as far as brackets of {@code width} bits settle it,
     * and null where the two brackets overlap and a tighter pair is what answers.
     *
     * <p>Everything this forms is an instrument, the two brackets and the numbers they are held against
     * alike, so a width the host has no room for anywhere in here is the run's shortage. The translation
     * is around the whole reading rather than around the step that happened to reach the host first:
     * which step that is depends on the width and on the values.
     */
    static @Nullable Integer magnitudeFromBrackets(ExactParts a, ExactParts b, int width) {
        try {
            Bracketed here = bracketedMagnitude(a, width);
            Bracketed there = bracketedMagnitude(b, width);
            if (compareShifted(here.low(), here.shift(), there.high(), there.shift()) > 0) {
                return 1;
            }
            if (compareShifted(here.high(), here.shift(), there.low(), there.shift()) < 0) {
                return -1;
            }
            return null;
        } catch (ArithmeticException e) {
            throw ExactPowers.hostShortage(e, "to compare at a width of " + width + " bits");
        }
    }

    /** A value's magnitude, held between two whole numbers of {@code width} bits. */
    static Bracketed bracketedMagnitude(ExactParts of, int width) {
        return bracketed(of, BigInteger.valueOf(of.twos()), BigInteger.valueOf(of.fives()), width);
    }

    /**
     * The magnitude of a value with {@code byTwos} and {@code byFives} standing in for its own
     * exponents, held between two whole numbers of about {@code width} bits.
     *
     * <p>The fraction is bracketed by one division rather than kept whole, which is what keeps every
     * number here to the working width. Taken at other exponents by the narrowing, which asks about a
     * value times a power of ten and so about exponents a scale has been added to.
     *
     * <p>A width the host has no room for leaves as the run's shortage and not as a value refused, so a
     * caller refining it is spared having to tell a shortage of room from a failure of the answer.
     */
    static Bracketed bracketed(ExactParts of, BigInteger byTwos, BigInteger byFives, int width) {
        try {
            Bracketed fraction = quotientBracketed(of.numerator().abs(), of.denominator(), width);
            if (byFives.signum() != 0) {
                Bracketed five = fiveTo(byFives.abs(), width);
                fraction = fraction.times(
                        byFives.signum() > 0 ? five : five.reciprocal(width), width);
            }
            return fraction.shiftedBy(byTwos);
        } catch (ArithmeticException e) {
            throw ExactPowers.hostShortage(e, "for a bracket of " + width + " bits");
        }
    }

    /**
     * {@code x / y} held between two whole numbers of about {@code width} bits, {@code x} being at least
     * nought and {@code y} above it.
     *
     * <p>Both sides are cut to the width first and what was cut off becomes part of the shift, so nothing
     * here is the size of either of them. A quotient's leading bits are decided by the leading bits of
     * the two numbers, and reaching them by moving the numerator up instead asks for room above it that a
     * stored fraction at the end of what the host holds does not have.
     */
    private static Bracketed quotientBracketed(BigInteger x, BigInteger y, int width) {
        Bracketed over = leadingBits(x, width);
        Bracketed under = leadingBits(y, width);
        return new Bracketed(
                over.low().shiftLeft(width).divide(under.high()),
                over.high().shiftLeft(width).divide(under.low()).add(BigInteger.ONE),
                over.shift().subtract(under.shift()).subtract(BigInteger.valueOf(width)));
    }

    /**
     * Where {@code a/b} stands against {@code c/d}, all four being above nought.
     *
     * <p>Exact, and never a product of any two of them. The whole parts of the two are compared, and where
     * those agree what is left over is compared the other way about — the greater remainder over the same
     * kind of thing makes the lesser fraction. That is the walk a common measure takes, so it ends in as
     * many steps as one does, and every number in it is a remainder of numbers already there.
     *
     * <p>Cross-multiplying instead asks for a number as large as two of them together, which refuses a
     * pair the host holds both sides of. A bracket asks for a width instead, and two fractions of one size
     * can stand a part in that size apart — closer than any width settled on ahead of the pair.
     */
    static int comparedAsFractions(BigInteger a, BigInteger b, BigInteger c, BigInteger d) {
        BigInteger up = a;
        BigInteger over = b;
        BigInteger against = c;
        BigInteger by = d;
        boolean theOtherWayAbout = false;
        while (true) {
            BigInteger[] here = up.divideAndRemainder(over);
            BigInteger[] there = against.divideAndRemainder(by);
            int byWhole = here[0].compareTo(there[0]);
            if (byWhole != 0) {
                return theOtherWayAbout ? -byWhole : byWhole;
            }
            boolean hereEnds = here[1].signum() == 0;
            boolean thereEnds = there[1].signum() == 0;
            if (hereEnds || thereEnds) {
                int ended = hereEnds ? (thereEnds ? 0 : -1) : 1;
                return theOtherWayAbout ? -ended : ended;
            }
            up = over;
            over = here[1];
            against = by;
            by = there[1];
            theOtherWayAbout = !theOtherWayAbout;
        }
    }

    /** A whole number's leading bits: what was cut off is the shift, and the number stands between the
     *  bits that are left and one more of them. */
    private static Bracketed leadingBits(BigInteger whole, int width) {
        int over = whole.bitLength() - width;
        if (over <= 0) {
            return Bracketed.exactly(whole);
        }
        BigInteger kept = whole.shiftRight(over);
        return new Bracketed(kept, kept.add(BigInteger.ONE), BigInteger.valueOf(over));
    }

    /**
     * Where {@code x × 2^a} stands against {@code y × 2^b}, both whole numbers being above nought.
     *
     * <p>Each side stands between its own count of bits and one more, so a gap of over one bit is read
     * off those counts and neither side is shifted — which is what keeps a shift no machine holds out
     * of this. Within a bit of one another, the two shifts are apart by no more than the bits the two
     * numbers hold, and the lesser side is lifted to meet the other.
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
     * {@code 5^exponent} bracketed to {@code width} bits, the exponent being at least nought.
     *
     * <p>Squared up from the exponent's bits, so the work is how many bits the exponent has and not
     * how large it is.
     */
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
     * A number held between two whole numbers a count of bits short of it: the number is at least
     * {@code low × 2^shift} and at most {@code high × 2^shift}.
     *
     * <p>Every step keeps the number between the two by rounding each end away from it, so what a
     * bracket says is true by how it was built rather than by an error anyone has to have got right.
     * What a width buys is how tight the bracket is, never whether it holds.
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
         * <p>The ends change places, the lower of the two coming from the upper of these. Nothing here is
         * larger than the width either: a one shifted up to meet an end and divided by it answers the
         * bits asked for, and the shift is the end's own size rather than anything's product.
         *
         * <p>The distance to shift by is a count of bits and is added as one. Added as an {@code int} it
         * wraps where the width and a bit length together run past what one counts, and a shift of a
         * negative count is a shift the other way, so what came of it was a bracket with the value outside
         * it rather than a refusal. That is an order answered wrongly, which is the one outcome no
         * instrument may have.
         */
        Bracketed reciprocal(int width) {
            int by = ExactPowers.bitsTheHostAddresses((long) width + high.bitLength());
            BigInteger over = BigInteger.ONE.shiftLeft(by);
            return new Bracketed(
                    over.divide(high), over.divide(low).add(BigInteger.ONE),
                    BigInteger.valueOf(-by).subtract(shift));
        }

        Bracketed shiftedBy(BigInteger bits) {
            return new Bracketed(low, high, shift.add(bits));
        }

        Bracketed squared(int width) {
            return new Bracketed(low.multiply(low), high.multiply(high), shift.add(shift))
                    .keptTo(width);
        }

        /** The same number, held between two numbers of no more than {@code width} bits. The lower end
         *  falls to where the shift leaves it and the upper end rises to the next one up, so the number
         *  stays inside. */
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
