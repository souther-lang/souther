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
 * it. Comparing decides from bounds on the logs wherever that settles it — which is what keeps
 * {@code r < 1} from spelling out a millionth — and falls back to exact whole numbers where they do
 * not. Powers of two and five come arbitrarily close in the log, so that fallback is reachable with
 * small numerators and is not bounded by them.
 */
public record Rational(BigInteger numerator, BigInteger denominator, long twos, long fives)
        implements Comparable<Rational> {

    /** Declared before the two values below, which are built by a constructor that reads it. */
    private static final BigInteger FIVE = BigInteger.valueOf(5);

    public static final Rational ZERO = new Rational(BigInteger.ZERO, BigInteger.ONE, 0, 0);
    public static final Rational ONE = new Rational(BigInteger.ONE, BigInteger.ONE, 0, 0);

    /**
     * Bounds on {@code log2 5}, scaled by {@link #LOG_SCALE}. The lower one is below the true value
     * and the upper one above it, which is what makes an interval built from them hold the number it
     * is about.
     */
    private static final long LOG2_FIVE_BELOW = 2321928;
    private static final long LOG2_FIVE_ABOVE = 2321929;
    private static final long LOG_SCALE = 1000000;

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
        return new Rational(
                numerator.divide(acrossOne).multiply(other.numerator.divide(acrossTwo)),
                denominator.divide(acrossTwo).multiply(other.denominator.divide(acrossOne)),
                added(twos, other.twos),
                added(fives, other.fives));
    }

    public Rational dividedBy(Rational other) {
        return times(other.reciprocal());
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
        BigInteger here = numerator.multiply(
                raised(distance(twos, commonTwos), distance(fives, commonFives)));
        BigInteger there = other.numerator.multiply(
                raised(distance(other.twos, commonTwos), distance(other.fives, commonFives)));
        BigInteger shared = denominator.gcd(other.denominator);
        BigInteger overThis = denominator.divide(shared);
        BigInteger sum = here.multiply(other.denominator.divide(shared)).add(there.multiply(overThis));
        return new Rational(sum, overThis.multiply(other.denominator), commonTwos, commonFives);
    }

    public Rational minus(Rational other) {
        return plus(other.negated());
    }

    /**
     * Where this stands against {@code other} by exact mathematical value.
     *
     * <p>Answered from the exponents wherever that settles it. The magnitudes are bracketed from the
     * bit lengths of the two fractions and from the exponents, and where the brackets do not overlap
     * the answer is read off them without a power being built — which is what a comparison of a
     * millionth against one is.
     *
     * <p>Where they do overlap the whole numbers are compared, and building them can cost what the
     * exponents say. Powers of two and five approach one another arbitrarily closely in the log, so
     * this is reachable for small numerators as well as large ones: the bracket is a way to answer
     * cheaply where the values are apart, not a bound on what answering costs.
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
        int byMagnitude = compareMagnitude(other);
        return signum() > 0 ? byMagnitude : -byMagnitude;
    }

    /** Where {@code |this|} stands against {@code |other|}, both being non-zero. */
    private int compareMagnitude(Rational other) {
        Integer fromBounds = magnitudeFromBounds(other);
        if (fromBounds != null) {
            return fromBounds;
        }
        long commonTwos = Math.min(twos, other.twos);
        long commonFives = Math.min(fives, other.fives);
        BigInteger here = numerator.abs()
                .multiply(other.denominator)
                .multiply(raised(distance(twos, commonTwos), distance(fives, commonFives)));
        BigInteger there = other.numerator.abs()
                .multiply(denominator)
                .multiply(raised(distance(other.twos, commonTwos), distance(other.fives, commonFives)));
        return here.compareTo(there);
    }

    /**
     * Where {@code |this|} stands against {@code |other|} as far as bounds on their logs settle it,
     * or null where the two brackets overlap and only the whole numbers answer.
     *
     * <p>Separate from the comparison so that both of its answers are asked for directly. A bracket
     * that never decided would leave every comparison correct and every one of them paying for a
     * power, and a comparison is the reader that cannot tell the two apart.
     *
     * <p>Null as well where the bracket's own arithmetic runs off the end of a sixty-four-bit number,
     * which exponents a run of multiplications reached can do. The exact comparison answers those,
     * and what it costs is what building the powers costs.
     */
    @Nullable Integer magnitudeFromBounds(Rational other) {
        try {
            if (lowerLog(this) > upperLog(other)) {
                return 1;
            }
            if (upperLog(this) < lowerLog(other)) {
                return -1;
            }
        } catch (ArithmeticException _) {
            return null;
        }
        return null;
    }

    /** A number {@code log2 |r|} is at least, scaled by {@link #LOG_SCALE}. */
    private static long lowerLog(Rational r) {
        return Math.addExact(
                Math.subtractExact(
                        Math.multiplyExact(r.numerator.abs().bitLength() - 1L, LOG_SCALE),
                        Math.multiplyExact((long) r.denominator.bitLength(), LOG_SCALE)),
                Math.addExact(Math.multiplyExact(r.twos, LOG_SCALE), fivesInLog(r.fives, true)));
    }

    /** A number {@code log2 |r|} is below, scaled by {@link #LOG_SCALE}. */
    private static long upperLog(Rational r) {
        return Math.addExact(
                Math.subtractExact(
                        Math.multiplyExact((long) r.numerator.abs().bitLength(), LOG_SCALE),
                        Math.multiplyExact(r.denominator.bitLength() - 1L, LOG_SCALE)),
                Math.addExact(Math.multiplyExact(r.twos, LOG_SCALE), fivesInLog(r.fives, false)));
    }

    /** What the power of five contributes to a bound on the log. Which of the two bounds on
     *  {@code log2 5} makes a number smaller depends on the sign of the exponent, so the side being
     *  built decides which is taken. */
    private static long fivesInLog(long fives, boolean below) {
        long bound = (fives >= 0) == below ? LOG2_FIVE_BELOW : LOG2_FIVE_ABOVE;
        return Math.multiplyExact(fives, bound);
    }

    /** {@code 2^twos × 5^fives}, both exponents being non-negative. */
    private static BigInteger raised(long twos, long fives) {
        BigInteger of = BigInteger.ONE.shiftLeft(buildable(twos));
        return fives == 0 ? of : of.multiply(FIVE.pow(buildable(fives)));
    }

    /** How far {@code from} stands above {@code down}, which is never negative and is the size of a
     *  power about to be built. */
    private static long distance(long from, long down) {
        return Math.subtractExact(from, down);
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
     */
    public @Nullable BigDecimal asDecimal() {
        if (!hasFiniteDecimal()) {
            return null;
        }
        long scale = Math.max(0, Math.max(negated(twos), negated(fives)));
        return new BigDecimal(
                numerator.multiply(raised(added(twos, scale), added(fives, scale))),
                buildable(scale));
    }

    /** This as a whole number where it is one, and null where it is not. */
    public @Nullable BigInteger asWholeNumber() {
        return isWhole() ? numerator.multiply(raised(twos, fives)) : null;
    }

    /**
     * This as a decimal of {@code scale} places, rounded by {@code towards}.
     *
     * <p>Where a caller must have a decimal whatever the value is.
     *
     * <p><b>The power of ten stays a scale.</b> What the two exponents have in common is a power of
     * ten, and a decimal already holds one of those as its scale — so it is moved there rather than
     * built. Multiplied out instead, a compact decimal that entered exact arithmetic and came back out
     * of it paid for every digit of its scale on the way, which is the cost this representation exists
     * to keep from being paid.
     *
     * <p>What is left is the part ten is not made of, and it is built: the fraction that remains is
     * the size of the answer at the scale asked for.
     *
     * <p>A scale far from the value's own is where this stops. Rounding {@code 1E-1000000000} to a
     * whole number is a rescaling {@code BigDecimal} refuses, so the operation aborts — which is what
     * {@code Decimal.toInt} does with the same decimal, for the same reason and at the same place.
     */
    public BigDecimal asDecimal(int scale, java.math.RoundingMode towards) {
        long tens = Math.min(twos, fives);
        BigInteger up = numerator.multiply(raised(distance(twos, tens), distance(fives, tens)));
        return new BigDecimal(up, asAScale(tens))
                .divide(new BigDecimal(denominator), scale, towards);
    }

    /** A power of ten as the scale that holds it, which is its negation. A scale is thirty-two bits,
     *  so a power past that is one no decimal holds — and it aborts rather than being built into the
     *  digits, which is the one thing this is here to avoid. */
    private static int asAScale(long tens) {
        long scale = negated(tens);
        if (scale < Integer.MIN_VALUE || scale > Integer.MAX_VALUE) {
            throw new ConstraintViolation("no Decimal holds a scale of " + scale);
        }
        return (int) scale;
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
