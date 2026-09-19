package souther.runtime;

import org.jspecify.annotations.Nullable;

import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * An exact rational, which is what {@code /} answers (spec §primitives). Neither {@code Int} nor
 * {@code Decimal} is closed under division, so a quotient that stays in the operand type needs an
 * unstated loss policy; this is the type that needs none.
 *
 * <p>The value is:
 *
 * <pre>{@code
 * numerator × 2^twos × 5^fives / denominator
 * }</pre>
 *
 * <p><b>Why the powers of two and five stand apart.</b> A {@code Decimal} is an unscaled whole number
 * over a power of ten, and a scale of a million is four bytes. Held as a plain numerator over a
 * denominator, embedding that decimal means building {@code 10^1000000} — a compact value becoming
 * work proportional to its scale by nothing more than entering exact arithmetic. So the factors ten is
 * made of are kept as exponents, and a decimal is taken in by two integer subtractions.
 *
 * <p>Ten is not enough on its own: a single power of ten cannot hold a half, whose only factor is a
 * two, and the two exponents of a value like a sixth are not equal. Two and five are therefore
 * separate, and what is left over — a third's three — stays in the numerator and the denominator.
 *
 * <p><b>One representation per value.</b> Every non-zero rational is uniquely {@code n/d · 2^a · 5^b}
 * where {@code n} and {@code d} are coprime and neither is divisible by two or by five: {@code a} is
 * the value's two-adic valuation, {@code b} its five-adic one, and what remains is a fraction in
 * lowest terms. So this record's own {@code equals} and {@code hashCode} are the language's equality
 * and hash, and {@link Values} reaches them through the arm that asks a value for itself. A
 * representation with a choice in it would have needed a rule there instead, and a container keyed by
 * one of these would have depended on which spelling arrived.
 *
 * <p><b>Why the exponents are sixty-four bits.</b> Every {@code Int} and every {@code Decimal} has one
 * exact value here, and that is a rule rather than a range this type happens to cover (ADR-0116). A
 * {@code Decimal}'s scale is thirty-two bits and enters as its negation, and negating the least
 * thirty-two-bit number leaves it — so an exponent held to a scale's own width would refuse a decimal
 * the widening is supposed to take, and stripping a factor of two out of the numerator would push one
 * more past the end. What a computation can ask for past this width aborts, as an {@code Int}'s
 * overflow does (spec §jvm-abort).
 *
 * <p><b>What the exponents cost.</b> Multiplying and dividing add and subtract them and never build
 * them, so scale stays free across both. Adding does build the difference between two exponents,
 * because that is what the exact sum is: {@code 1 + 1E-1000000} has a million digits whatever holds
 * it. Comparing builds nothing at all: a power of two is a count of bits and a power of five is
 * bracketed by squaring, so what a comparison costs is the bits of an exponent and not its size —
 * which is what keeps {@code r < 1} from spelling out a millionth, and what makes the order answered
 * for every pair rather than for the pairs whose digits happen to fit.
 *
 * <p><b>What a step is allowed to refuse.</b> An operation aborts where the answer has no
 * representation here, and not where a step on the way to it has none. The two are easy to confuse
 * because the shapes that separate them are at the ends of the exponent's range, which a run of
 * squarings reaches and an ordinary model does not: a quotient's exponents are the difference of two
 * held ones and a reciprocal's are a negation, so division that went by the reciprocal refused
 * {@code r / r}; a decimal's scale is signed, so a narrowing that took a non-negative one built the
 * power a compact decimal had carried as its scale; a rounding policy is asked for so that a value
 * comes back, so reading it off the digits refused values it was named to answer. Each of those is a
 * middle step narrower than the value it was handed.
 *
 * <p>The order is the case where that rule bites hardest, because an order always exists: the pairs
 * whose logs sit closest together are the ones whose digits are largest, so a comparison that fell
 * back to the digits would refuse exactly the pairs it was reached for. None of it is built.
 *
 * <p><b>The host's own limits leave by this type's abort.</b> A whole number is held by a host that has
 * a largest one, and a number past it is one no value here is made of — so no method of this type
 * answers with an exception of the host's arithmetic, which says nothing about a Rational to whoever
 * reads it (ADR-0112). The translation is here and not at the operators, because it is here that the
 * host is reached: {@code List.sum} over these asks this type for a sum directly, and an operator that
 * caught what it never called would have left the fold answering the other way.
 */
public record Rational(BigInteger numerator, BigInteger denominator, long twos, long fives)
        implements Comparable<Rational> {

    /** Declared before the two values below, which are built by a constructor that reads it. */
    private static final BigInteger FIVE = BigInteger.valueOf(5);

    public static final Rational ZERO = new Rational(BigInteger.ZERO, BigInteger.ONE, 0, 0);
    public static final Rational ONE = new Rational(BigInteger.ONE, BigInteger.ONE, 0, 0);

    /**
     * How many bits a power of five is first bracketed to when a comparison asks for one.
     *
     * <p>A starting point and not a limit: a bracket too wide to separate the pair it was taken for is
     * taken again at twice this. Wide enough that the second turn is not reached by any pair a
     * comparison is likely to be asked about — the exponents would have to put the two values within
     * this many bits of one another — and small enough that the first turn is a few dozen
     * multiplications of numbers this size.
     */
    private static final int BRACKET_BITS = 128;

    /**
     * How many bits of a value {@link #toString} will spell out. A rational's plain spelling is as
     * long as the number is, and a millionth of a millionth is not something a message is improved
     * by carrying — the same reason a {@code Decimal} at the ends of its scale range is described
     * rather than spelled (spec §jvm-abort). Beyond this the factored form is printed, which is
     * bounded by the size of what is stored.
     */
    private static final int SPELLED_BITS = 3322;

    public Rational {
        if (numerator == null || denominator == null) {
            throw new IllegalArgumentException("a rational is two whole numbers and two exponents");
        }
        if (denominator.signum() == 0) {
            throw new IllegalArgumentException("a rational has no zero denominator: " + numerator + "/0");
        }
        if (numerator.signum() == 0) {
            denominator = BigInteger.ONE;
            twos = 0;
            fives = 0;
        } else {
            if (denominator.signum() < 0) {
                numerator = numerator.negate();
                denominator = denominator.negate();
            }
            BigInteger common = numerator.gcd(denominator);
            if (!common.equals(BigInteger.ONE)) {
                numerator = numerator.divide(common);
                denominator = denominator.divide(common);
            }
            // The two sides are coprime by now, so a factor of two or of five is on one of them
            // alone, and taking it off one cannot put it back on the other.
            int inNumerator = numerator.getLowestSetBit();
            if (inNumerator > 0) {
                numerator = numerator.shiftRight(inNumerator);
                twos = added(twos, inNumerator);
            }
            int inDenominator = denominator.getLowestSetBit();
            if (inDenominator > 0) {
                denominator = denominator.shiftRight(inDenominator);
                twos = added(twos, -inDenominator);
            }
            // One five at a time, which costs a division per trailing zero of the number it is taking
            // them off. That is bounded by the digits the number already has, so nothing here is
            // amplified by the exponents this type carries — a power of ten held as a scale never
            // reaches this loop at all.
            while (true) {
                BigInteger[] divided = numerator.divideAndRemainder(FIVE);
                if (divided[1].signum() != 0) {
                    break;
                }
                numerator = divided[0];
                fives = added(fives, 1);
            }
            while (true) {
                BigInteger[] divided = denominator.divideAndRemainder(FIVE);
                if (divided[1].signum() != 0) {
                    break;
                }
                denominator = divided[0];
                fives = added(fives, -1);
            }
        }
    }

    /** The rational a whole number is. */
    public static Rational of(long whole) {
        return new Rational(BigInteger.valueOf(whole), BigInteger.ONE, 0, 0);
    }

    /** The rational a ratio of two whole numbers is. */
    public static Rational of(BigInteger numerator, BigInteger denominator) {
        return new Rational(numerator, denominator, 0, 0);
    }

    /**
     * The rational a written decimal is, exactly.
     *
     * <p>A decimal with scale {@code s} is its unscaled value over {@code 10^s}, which is that value
     * times {@code 2^-s} times {@code 5^-s}. The scale reaches the exponents and nothing is built
     * from it, so a decimal compact in its own representation stays compact here — and every decimal
     * has one of these, the negation of a thirty-two-bit scale being a sixty-four-bit exponent.
     */
    public static Rational of(BigDecimal written) {
        long exponent = -(long) written.scale();
        return new Rational(written.unscaledValue(), BigInteger.ONE, exponent, exponent);
    }

    public boolean isZero() {
        return numerator.signum() == 0;
    }

    public int signum() {
        return numerator.signum();
    }

    /** Whether this is a whole number — which, in lowest terms with no two and no five left in the
     *  denominator, is the denominator being one and neither exponent being negative. */
    public boolean isWhole() {
        return denominator.equals(BigInteger.ONE) && twos >= 0 && fives >= 0;
    }

    /** Whether this has a finite decimal spelling. A denominator in lowest terms that no longer holds
     *  a two or a five holds something ten is not made of, and a fraction over it repeats. */
    public boolean hasFiniteDecimal() {
        return denominator.equals(BigInteger.ONE);
    }

    public Rational negated() {
        return new Rational(numerator.negate(), denominator, twos, fives);
    }

    /** One over this. Refused for nought, which has no reciprocal — a caller reaching this from
     *  {@code /} says what a zero divisor is where the operator is emitted. */
    public Rational reciprocal() {
        if (isZero()) {
            throw new IllegalArgumentException("nought has no reciprocal");
        }
        return new Rational(denominator, numerator, negated(twos), negated(fives));
    }

    /**
     * The product. The exponents add and are never built, and the common factors of the two fractions
     * are taken off before the numerators and denominators are multiplied, so what is multiplied is
     * no larger than the answer.
     */
    public Rational times(Rational other) {
        if (isZero() || other.isZero()) {
            return ZERO;
        }
        BigInteger acrossOne = numerator.gcd(other.denominator);
        BigInteger acrossTwo = other.numerator.gcd(denominator);
        try {
            return new Rational(
                    numerator.divide(acrossOne).multiply(other.numerator.divide(acrossTwo)),
                    denominator.divide(acrossTwo).multiply(other.denominator.divide(acrossOne)),
                    added(twos, other.twos),
                    added(fives, other.fives));
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    /**
     * The quotient. The exponents subtract and are never built, and the cross factors come off before
     * the multiplication, as they do for the product.
     *
     * <p>Not one over the divisor, multiplied in. A reciprocal's exponents are the divisor's negated,
     * and the least sixty-four-bit number has no positive counterpart — so a quotient reached that way
     * refused pairs whose own exponents are the difference of two held ones, with {@code r / r} among
     * them. The difference is what the answer's exponents are, so it is what is computed.
     */
    public Rational dividedBy(Rational other) {
        if (other.isZero()) {
            throw new IllegalArgumentException("nought divides nothing");
        }
        if (isZero()) {
            return ZERO;
        }
        BigInteger acrossOne = numerator.gcd(other.numerator);
        BigInteger acrossTwo = denominator.gcd(other.denominator);
        try {
            return new Rational(
                    numerator.divide(acrossOne).multiply(other.denominator.divide(acrossTwo)),
                    denominator.divide(acrossTwo).multiply(other.numerator.divide(acrossOne)),
                    lessened(twos, other.twos),
                    lessened(fives, other.fives));
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    /**
     * The sum.
     *
     * <p>The lesser of each pair of exponents is common to both terms and stays an exponent. What is
     * left is the distance between them, and that is built: the exact sum of two values whose
     * exponents are far apart is a number with that many digits in it, and no representation of the
     * answer is smaller than the answer.
     *
     * <p>The denominators' common factor is taken off before either is multiplied out, so the
     * intermediate is the size of the result rather than of the product of the two denominators.
     */
    public Rational plus(Rational other) {
        if (isZero()) {
            return other;
        }
        if (other.isZero()) {
            return this;
        }
        long commonTwos = Math.min(twos, other.twos);
        long commonFives = Math.min(fives, other.fives);
        try {
            BigInteger here = numerator.multiply(
                    raised(lessened(twos, commonTwos), lessened(fives, commonFives)));
            BigInteger there = other.numerator.multiply(
                    raised(lessened(other.twos, commonTwos), lessened(other.fives, commonFives)));
            BigInteger shared = denominator.gcd(other.denominator);
            BigInteger overThis = denominator.divide(shared);
            BigInteger sum =
                    here.multiply(other.denominator.divide(shared)).add(there.multiply(overThis));
            return new Rational(sum, overThis.multiply(other.denominator), commonTwos, commonFives);
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    public Rational minus(Rational other) {
        return plus(other.negated());
    }

    /**
     * Where this stands against {@code other} by exact mathematical value.
     *
     * <p>Answered for every pair this type holds, and no power is ever built to answer it. What the
     * two values are made of beyond their stored fractions is a power of two, which is a count of
     * bits, and a power of five, which is bracketed between two whole numbers of a working width by
     * squaring — so the work is the bits of an exponent rather than its size, and a comparison of a
     * millionth of a millionth against one costs a few dozen multiplications of numbers that width.
     *
     * <p>Where a bracket is too wide to separate the pair it is taken again at twice the width. That
     * ends, because two values with one canonical representation each are equal exactly where those
     * representations are, and unequal ones stand a fixed distance apart for a bracket to get inside
     * of. Which is the whole of why this is answered from brackets rather than from the numbers: the
     * exponents run to sixty-four bits, so the pairs whose logs sit closest together are also the ones
     * whose digits no machine holds.
     */
    @Override
    public int compareTo(Rational other) {
        if (equals(other)) {
            return 0;
        }
        int bySign = Integer.compare(signum(), other.signum());
        if (bySign != 0) {
            return bySign;
        }
        try {
            int byMagnitude = compareMagnitude(other);
            return signum() > 0 ? byMagnitude : -byMagnitude;
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    /**
     * Where {@code |this|} stands against {@code |other|}, both being non-zero.
     *
     * <p>The fractions are cross-multiplied, which is the size of what is stored, and what is left of
     * the two values is one power of two and one power of five — the differences of the two pairs of
     * exponents, each taken once and put on the side its sign belongs to.
     *
     * <p>The two magnitudes are unequal, which is what makes the refinement end. The caller has that:
     * one canonical representation per value means two values of one magnitude and one sign are the same
     * record, and the comparison above answered those before reaching here.
     */
    private int compareMagnitude(Rational other) {
        if (fives == other.fives) {
            // No power of five between them, so the count of bits is the whole of the difference.
            return compareShifted(
                    numerator.abs().multiply(other.denominator), apart(twos, other.twos),
                    other.numerator.abs().multiply(denominator), BigInteger.ZERO);
        }
        // The width stops rising where a count of bits does. Reaching that means the two values agree
        // over more bits than a bracket is addressed in, which takes stored fractions far larger than
        // the machine bracketing them — so this is where memory runs out rather than a value's range,
        // and it says so instead of doubling into a negative width.
        for (int width = BRACKET_BITS; width > 0; width += width) {
            Integer decided = magnitudeFromBrackets(other, width);
            if (decided != null) {
                return decided;
            }
        }
        throw new ConstraintViolation("no bracket this machine holds separates " + this + " from " + other);
    }

    /**
     * Where {@code |this|} stands against {@code |other|} as far as brackets of {@code width} bits
     * settle it, and null where the two brackets overlap and a tighter pair is what answers.
     *
     * <p>Separate from the comparison above so that both of its answers are asked for directly. A
     * width that always overlapped would leave the comparison correct and looping, and a width that
     * always decided would leave the refinement above it unreached — a comparison is the reader that
     * cannot tell either from a bracket that works.
     */
    @Nullable Integer magnitudeFromBrackets(Rational other, int width) {
        BigInteger here = numerator.abs().multiply(other.denominator);
        BigInteger there = other.numerator.abs().multiply(denominator);
        BigInteger byFives = apart(fives, other.fives);
        Bracketed five = fiveTo(byFives.abs(), width);
        boolean fivesAreHere = byFives.signum() > 0;
        Bracketed left = (fivesAreHere ? five.times(here) : Bracketed.exactly(here))
                .shiftedBy(apart(twos, other.twos));
        Bracketed right = fivesAreHere ? Bracketed.exactly(there) : five.times(there);
        if (compareShifted(left.low(), left.shift(), right.high(), right.shift()) > 0) {
            return 1;
        }
        if (compareShifted(left.high(), left.shift(), right.low(), right.shift()) < 0) {
            return -1;
        }
        return null;
    }

    /** How far one exponent stands from another, which no exponent's own width holds. */
    private static BigInteger apart(long exponent, long from) {
        return BigInteger.valueOf(exponent).subtract(BigInteger.valueOf(from));
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
     * how large it is: a power of five whose digits no machine holds is bracketed here in as many
     * multiplications of numbers this wide as the exponent has bits.
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
    private record Bracketed(BigInteger low, BigInteger high, BigInteger shift) {

        static Bracketed exactly(BigInteger whole) {
            return new Bracketed(whole, whole, BigInteger.ZERO);
        }

        Bracketed times(BigInteger by) {
            return new Bracketed(low.multiply(by), high.multiply(by), shift);
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

    /** {@code 2^twos × 5^fives}, both exponents being non-negative. */
    private static BigInteger raised(long twos, long fives) {
        int byTwos = buildable(twos);
        int byFives = buildable(fives);
        heldByTheHost(byTwos + 2L * byFives);
        BigInteger of = BigInteger.ONE.shiftLeft(byTwos);
        return byFives == 0 ? of : of.multiply(FIVE.pow(byFives));
    }

    /**
     * That a whole number of this many bits is one the host holds, asked before it is built.
     *
     * <p>A {@code BigInteger} is addressed by a count of bits, so there is a size past which the host has
     * none — and a whole number the host cannot hold is one no value of this type is made of either. So
     * the refusal belongs to this type and leaves by its own abort, the way an exponent past its width
     * does. Reached instead by building the number, the host says it by an exception of its arithmetic,
     * which says nothing about a Rational to whoever reads it (ADR-0112) and does not say it quickly: a
     * power of five the host has no room for is not refused on sight but computed until it does not fit,
     * which is minutes and hundreds of megabytes for an answer that was never going to come.
     *
     * <p>The count is under the truth rather than over it — a factor of five counted as two bits when it
     * is nearer two and a third — so this refuses nothing the host would have held, and what the
     * under-count lets through is refused by the host and translated where it is caught.
     */
    private static void heldByTheHost(long bits) {
        if (bits > Integer.MAX_VALUE) {
            throw new ConstraintViolation("no Rational holds a whole number of " + bits + " bits");
        }
    }

    /**
     * The abort a whole number the host had no range for leaves by.
     *
     * <p>Every method of this type that computes translates it, and the translation is here rather than
     * at the operators in {@link RationalMath} because it is here that the host is reached: a list folded
     * with {@code List.sum} asks this type for a sum directly, so a translation at the operator alone
     * would leave the fold answering with an exception of the host's arithmetic.
     */
    private static ConstraintViolation noRoomForIt(ArithmeticException thrown) {
        return new ConstraintViolation("no Rational holds a whole number that size: " + thrown.getMessage());
    }

    /** Two exponents subtracted, or the abort of a computation asking for one past what is held. The
     *  difference of two exponents is the quotient's as much as their sum is the product's, so it is
     *  held to the same width and leaves it the same way — and never by an exception of the arithmetic
     *  it was computed with, which says nothing about a Rational to whoever reads it. */
    private static long lessened(long exponent, long by) {
        try {
            return Math.subtractExact(exponent, by);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Rational exponent out of range: " + exponent + " - " + by);
        }
    }

    /** Two exponents added, or the abort of a computation asking for one past what is held. Sixty-four
     *  bits is the exponent's width, and a value needing more of it has no representation here rather
     *  than a rounded one. */
    private static long added(long exponent, long by) {
        try {
            return Math.addExact(exponent, by);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Rational exponent out of range: " + exponent + " + " + by);
        }
    }

    /** An exponent negated, which the least sixty-four-bit number is not. */
    private static long negated(long exponent) {
        try {
            return Math.negateExact(exponent);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Rational exponent out of range: -(" + exponent + ")");
        }
    }

    /** An exponent as a power something is about to be built to. A power of two past what a positive
     *  {@code int} counts is one no machine holds the digits of, so it aborts here rather than
     *  answering a number it could not have built. */
    private static int buildable(long exponent) {
        if (exponent < 0 || exponent > Integer.MAX_VALUE) {
            throw new ConstraintViolation("no Rational is built at a power of " + exponent);
        }
        return (int) exponent;
    }

    /**
     * This as a decimal where it has one exactly, and null where it has none. A caller that must
     * answer with a decimal whatever the value states its rounding at the point it asks.
     *
     * <p>What the two exponents have in common is a power of ten and goes to the scale, whichever way
     * it points — a decimal's scale is signed, and a value made of powers above nought is as compact a
     * decimal as one made of powers below it. Held to a non-negative scale instead, the way out was
     * narrower than the way in: a decimal that became one of these came back only by building the power
     * of ten it had arrived carrying as its scale, which is the work this representation exists to
     * avoid, and past what a machine holds it did not come back at all.
     */
    public @Nullable BigDecimal asDecimal() {
        if (!hasFiniteDecimal()) {
            return null;
        }
        // The scale first, which is the question about the answer; the digits after, which are the work.
        int scale = aScaleThatClearsBothExponents();
        try {
            return new BigDecimal(
                    numerator.multiply(raised(added(twos, scale), added(fives, scale))), scale);
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    /**
     * A scale the decimal this exactly is can be written at.
     *
     * <p>A decimal of scale {@code s} is a whole number over {@code 10^s}, and that whole number is this
     * value's numerator with {@code 2^(twos + s)} and {@code 5^(fives + s)} multiplied into it. So every
     * {@code s} leaving both of those at or above nought writes the value, and which one is taken is a
     * choice rather than the answer: the least of them is the most compact decimal there is for the
     * value, and the ones above it are the same value with the rest of the two powers in its digits.
     *
     * <p>Which is why the least one is not simply taken. A scale is thirty-two bits, and the least scale
     * there is stands above the least power of ten a value of this type can be made of — so a value whose
     * most compact decimal is past that end still has a decimal, written at the least scale a decimal
     * holds with what is left of the powers in the digits. Taking the compact one and no other refused
     * values that had arrived as decimals, which is the one thing the widening promises to be reversible
     * for.
     *
     * <p>The other end is where a value really has no decimal: a scale counts only so far up, and a
     * value needing more places than that is not one any spelling reaches.
     */
    private int aScaleThatClearsBothExponents() {
        long tens = Math.min(twos, fives);
        if (tens < -(long) Integer.MAX_VALUE) {
            throw new ConstraintViolation(
                    "no Decimal holds a scale of " + BigInteger.valueOf(tens).negate());
        }
        return tens > -(long) Integer.MIN_VALUE ? Integer.MIN_VALUE : (int) -tens;
    }

    /** This as a whole number where it is one, and null where it is not. */
    public @Nullable BigInteger asWholeNumber() {
        if (!isWhole()) {
            return null;
        }
        try {
            return numerator.multiply(raised(twos, fives));
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    /**
     * This as a decimal of {@code scale} places, rounded by {@code towards}.
     *
     * <p>Where a caller must have a decimal whatever the value is.
     *
     * <p><b>The scale goes to the exponents, not the digits.</b> A decimal of {@code scale} places is a
     * whole number over {@code 10^scale}, so what is asked for is the whole number this rounds to when
     * multiplied by that power — and multiplying by it moves the two exponents. So the rounding is done
     * on the factored value and the answer is that whole number beside the scale it was asked at.
     *
     * <p>Not a decimal built and then rounded. What a value's own exponents say has nothing to do with
     * how large the answer is: a value made of a power of two over a power of five that all but cancel
     * stands near one, and spelling it out first asks for digits the answer does not have and no machine
     * holds. Which is the same reason the order is answered from brackets, and the brackets are what
     * this reads too.
     */
    public BigDecimal asDecimal(int scale, java.math.RoundingMode towards) {
        if (isZero()) {
            return new BigDecimal(BigInteger.ZERO, scale);
        }
        try {
            return new BigDecimal(roundedTimesTenTo(scale, towards), scale);
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    /**
     * The whole number {@code this × 10^scale} rounds to by {@code towards}, which is the unscaled value
     * of this at that scale.
     *
     * <p>Multiplying by the power of ten adds the scale to both exponents, and the sum is held wider than
     * an exponent is: a value whose own exponent is at the end of its range has an ordinary answer at an
     * ordinary scale, so this is one of the places where what an intermediate holds must not be what the
     * answer is allowed to be.
     *
     * <p>Two shapes are read off the exponents rather than bracketed, because a bracket can never say
     * that a value <i>is</i> a whole number or <i>is</i> exactly half of one, and the policies part
     * company at exactly half. In lowest terms with no two and no five left beside the fraction, the
     * value is a whole number exactly where the denominator is one and both exponents have reached
     * nought, and it is half of one exactly where the same holds of twice it.
     */
    private BigInteger roundedTimesTenTo(int scale, java.math.RoundingMode towards) {
        BigInteger byTwos = atTenTo(twos, scale);
        BigInteger byFives = atTenTo(fives, scale);
        BigInteger magnitude = numerator.abs();
        boolean overOne = denominator.equals(BigInteger.ONE);
        if (overOne && byTwos.signum() >= 0 && byFives.signum() >= 0) {
            // A whole number already, so there is no fraction for a policy to have an opinion about.
            return signedLike(builtFrom(magnitude, byTwos, byFives));
        }
        BigInteger byTwiceTheTwos = byTwos.add(BigInteger.ONE);
        if (overOne && byTwiceTheTwos.signum() >= 0 && byFives.signum() >= 0) {
            // Twice it is a whole number and it is not, so it stands at exactly half of one.
            BigInteger twice = builtFrom(magnitude, byTwiceTheTwos, byFives);
            return roundedFrom(twice.shiftRight(1), 0, towards);
        }
        for (int width = BRACKET_BITS; width > 0; width += width) {
            Bracketed up = Bracketed.exactly(magnitude);
            Bracketed down = Bracketed.exactly(denominator);
            if (byFives.signum() > 0) {
                up = fiveTo(byFives, width).times(magnitude);
            } else if (byFives.signum() < 0) {
                down = fiveTo(byFives.negate(), width).times(denominator);
            }
            // Twice the value, so that one whole number carries both which two it stands between and
            // which side of half of the way it stands: its half is the one, its last bit the other.
            if (byTwiceTheTwos.signum() >= 0) {
                up = up.shiftedBy(byTwiceTheTwos);
            } else {
                down = down.shiftedBy(byTwiceTheTwos.negate());
            }
            BigInteger apart = up.shift().subtract(down.shift());
            BigInteger least = flooredQuotient(up.low(), down.high(), apart);
            BigInteger most = flooredQuotient(up.high(), down.low(), apart);
            if (least.equals(most)) {
                return roundedFrom(least.shiftRight(1), least.testBit(0) ? 1 : -1, towards);
            }
        }
        throw new ConstraintViolation("no bracket this machine holds rounds " + this);
    }

    /**
     * Which of {@code whole} and the next one up the value rounds to, the value standing {@code
     * againstHalf} of the way between them and neither being reached exactly.
     *
     * <p>Every policy of the seven reads the sign and that standing and nothing else, which is what makes
     * the digits beside the point. At exactly half of the way the two neighbours are this whole number
     * and the next, and the policy that takes the even one takes whichever of those is even.
     */
    private BigInteger roundedFrom(BigInteger whole, int againstHalf, java.math.RoundingMode towards) {
        boolean awayFromNought = switch (towards) {
            case UP -> true;
            case DOWN -> false;
            case CEILING -> signum() > 0;
            case FLOOR -> signum() < 0;
            case HALF_UP -> againstHalf >= 0;
            case HALF_DOWN -> againstHalf > 0;
            case HALF_EVEN -> againstHalf > 0 || (againstHalf == 0 && whole.testBit(0));
            case UNNECESSARY -> throw new ArithmeticException("Rounding necessary");
        };
        return signedLike(awayFromNought ? whole.add(BigInteger.ONE) : whole);
    }

    /** An exponent with a scale added, held wider than an exponent is — the scale reaches every value
     *  this type holds, so their sum is not bounded by what one of them is. */
    private static BigInteger atTenTo(long exponent, int scale) {
        return BigInteger.valueOf(exponent).add(BigInteger.valueOf(scale));
    }

    /** {@code whole × 2^twos × 5^fives}, both exponents being at least nought. What this builds is the
     *  answer's own digits, which is the one thing a narrowing is always allowed to ask for. */
    private static BigInteger builtFrom(BigInteger whole, BigInteger twos, BigInteger fives) {
        int byTwos = buildable(twos);
        int byFives = buildable(fives);
        heldByTheHost(whole.bitLength() + byTwos + 2L * byFives);
        return whole.shiftLeft(byTwos).multiply(FIVE.pow(byFives));
    }

    /** {@code floor(x × 2^byBits / y)}, {@code x} being at least nought and {@code y} above it. */
    private static BigInteger flooredQuotient(BigInteger x, BigInteger y, BigInteger byBits) {
        if (byBits.signum() >= 0) {
            return x.shiftLeft(buildable(byBits)).divide(y);
        }
        BigInteger down = byBits.negate();
        // Shifted down by more bits than the numerator has, the quotient is below one whatever the
        // denominator is — which is the shape a value far nearer nought than the scale counts takes, and
        // the shift itself is one no machine holds.
        if (down.compareTo(BigInteger.valueOf(x.bitLength())) > 0) {
            return BigInteger.ZERO;
        }
        return x.divide(y.shiftLeft(down.intValueExact()));
    }

    /** The same of an exponent held wider than one of this type's own, which the sum of an exponent and
     *  a scale is. */
    private static int buildable(BigInteger exponent) {
        if (exponent.signum() < 0 || exponent.bitLength() > Integer.SIZE - 1) {
            throw new ConstraintViolation("no Rational is built at a power of " + exponent);
        }
        return exponent.intValueExact();
    }

    /** A magnitude given this value's sign. */
    private BigInteger signedLike(BigInteger magnitude) {
        return signum() < 0 ? magnitude.negate() : magnitude;
    }

    /** The numerator with the powers that multiply it built in. */
    private BigInteger numeratorWithItsPowers() {
        return numerator.multiply(raised(atLeastNought(twos), atLeastNought(fives)));
    }

    /** The denominator with the powers that divide it built in. */
    private BigInteger denominatorWithItsPowers() {
        return denominator.multiply(raised(atLeastNought(negated(twos)), atLeastNought(negated(fives))));
    }

    /** {@code e} where it is above nought, and nought where it is not. */
    private static long atLeastNought(long e) {
        return Math.max(e, 0);
    }

    /**
     * The value, spelled as one fraction where it is small enough to read and as the factored form
     * where it is not.
     */
    @Override
    public String toString() {
        // The exponents first, and by their own ends rather than through a magnitude: the least
        // sixty-four-bit number has no positive counterpart, so a reading that took one would answer
        // about a value it had already left.
        if (twos > SPELLED_BITS || twos < -SPELLED_BITS
                || fives > SPELLED_BITS || fives < -SPELLED_BITS
                || (long) numerator.abs().bitLength() + denominator.bitLength() > SPELLED_BITS) {
            return numerator + "/" + denominator + "×2^" + twos + "×5^" + fives;
        }
        BigInteger up = numeratorWithItsPowers();
        BigInteger down = denominatorWithItsPowers();
        BigInteger common = up.gcd(down);
        if (common.signum() != 0 && !common.equals(BigInteger.ONE)) {
            up = up.divide(common);
            down = down.divide(common);
        }
        return down.equals(BigInteger.ONE) ? up.toString() : up + "/" + down;
    }
}
