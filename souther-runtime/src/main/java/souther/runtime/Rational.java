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
 * <p><b>What the exponents cost.</b> Multiplying and dividing add and subtract them and never build
 * them, so scale stays free across both. Adding does build the difference between two exponents,
 * because that is what the exact sum is: {@code 1 + 1E-1000000} has a million digits whatever holds
 * it. Comparing decides from the exponents alone wherever bounds on the magnitudes separate — which
 * is what keeps {@code r < 1} from spelling out a millionth — and falls back to exact whole numbers
 * where they do not. Powers of two and five come arbitrarily close in the log, so that fallback is
 * reachable with small numerators and is not bounded by them.
 *
 * <p>An exponent is a signed 32-bit number, the same resource a {@code Decimal} scale is, and a
 * computation that leaves that range aborts rather than answering (spec §jvm-abort).
 */
public record Rational(BigInteger numerator, BigInteger denominator, int twos, int fives)
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
                twos = exponent(twos + (long) inNumerator);
            }
            int inDenominator = denominator.getLowestSetBit();
            if (inDenominator > 0) {
                denominator = denominator.shiftRight(inDenominator);
                twos = exponent(twos - (long) inDenominator);
            }
            long fivesHere = fives;
            while (true) {
                BigInteger[] divided = numerator.divideAndRemainder(FIVE);
                if (divided[1].signum() != 0) {
                    break;
                }
                numerator = divided[0];
                fivesHere++;
            }
            while (true) {
                BigInteger[] divided = denominator.divideAndRemainder(FIVE);
                if (divided[1].signum() != 0) {
                    break;
                }
                denominator = divided[0];
                fivesHere--;
            }
            fives = exponent(fivesHere);
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
     * from it, so a decimal compact in its own representation stays compact here.
     */
    public static Rational of(BigDecimal written) {
        int scale = written.scale();
        int exponent = exponent(-(long) scale);
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
        return new Rational(denominator, numerator, exponent(-(long) twos), exponent(-(long) fives));
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
                exponent(twos + (long) other.twos),
                exponent(fives + (long) other.fives));
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
        int commonTwos = Math.min(twos, other.twos);
        int commonFives = Math.min(fives, other.fives);
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
        int commonTwos = Math.min(twos, other.twos);
        int commonFives = Math.min(fives, other.fives);
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
     */
    @Nullable Integer magnitudeFromBounds(Rational other) {
        if (lowerLog(this) > upperLog(other)) {
            return 1;
        }
        if (upperLog(this) < lowerLog(other)) {
            return -1;
        }
        return null;
    }

    /** A number {@code log2 |r|} is at least, scaled by {@link #LOG_SCALE}. */
    private static long lowerLog(Rational r) {
        return (r.numerator.abs().bitLength() - 1L) * LOG_SCALE
                - (long) r.denominator.bitLength() * LOG_SCALE
                + r.twos * LOG_SCALE
                + fivesInLog(r.fives, true);
    }

    /** A number {@code log2 |r|} is below, scaled by {@link #LOG_SCALE}. */
    private static long upperLog(Rational r) {
        return (long) r.numerator.abs().bitLength() * LOG_SCALE
                - (r.denominator.bitLength() - 1L) * LOG_SCALE
                + r.twos * LOG_SCALE
                + fivesInLog(r.fives, false);
    }

    /** What the power of five contributes to a bound on the log. Which of the two bounds on
     *  {@code log2 5} makes a number smaller depends on the sign of the exponent, so the side being
     *  built decides which is taken. */
    private static long fivesInLog(int fives, boolean below) {
        long bound = (fives >= 0) == below ? LOG2_FIVE_BELOW : LOG2_FIVE_ABOVE;
        return fives * bound;
    }

    /** {@code 2^twos × 5^fives}, both exponents being non-negative. */
    private static BigInteger raised(int twos, int fives) {
        BigInteger of = BigInteger.ONE.shiftLeft(twos);
        return fives == 0 ? of : of.multiply(FIVE.pow(fives));
    }

    /** How far {@code from} stands above {@code down}, which is never negative and is the size of a
     *  power about to be built. */
    private static int distance(int from, int down) {
        return exponent(from - (long) down);
    }

    /** An exponent held to what one is, or the abort of a computation asking for one that is not.
     *  Thirty-two bits is the resource a scale is, and a value needing more of it has no
     *  representation here rather than a rounded one. */
    private static int exponent(long asked) {
        if (asked < Integer.MIN_VALUE || asked > Integer.MAX_VALUE) {
            throw new ConstraintViolation("Rational exponent out of range: " + asked);
        }
        return (int) asked;
    }

    /**
     * This as a decimal where it has one exactly, and null where it has none. A caller that must
     * answer with a decimal whatever the value states its rounding at the point it asks.
     */
    public @Nullable BigDecimal asDecimal() {
        if (!hasFiniteDecimal()) {
            return null;
        }
        int scale = exponent(Math.max(0, Math.max(-(long) twos, -(long) fives)));
        return new BigDecimal(
                numerator.multiply(raised(exponent(twos + (long) scale), exponent(fives + (long) scale))),
                scale);
    }

    /** This as a whole number where it is one, and null where it is not. */
    public @Nullable BigInteger asWholeNumber() {
        return isWhole() ? numerator.multiply(raised(twos, fives)) : null;
    }

    /**
     * The value, spelled as one fraction where it is small enough to read and as the factored form
     * where it is not.
     */
    @Override
    public String toString() {
        long bits = (long) numerator.abs().bitLength() + denominator.bitLength()
                + Math.abs((long) twos) + Math.abs(fives * LOG2_FIVE_ABOVE / LOG_SCALE);
        if (bits > SPELLED_BITS) {
            return numerator + "/" + denominator + "×2^" + twos + "×5^" + fives;
        }
        BigInteger up = numerator.multiply(raised(Math.max(twos, 0), Math.max(fives, 0)));
        BigInteger down = denominator.multiply(raised(Math.max(-twos, 0), Math.max(-fives, 0)));
        BigInteger common = up.gcd(down);
        if (common.signum() != 0 && !common.equals(BigInteger.ONE)) {
            up = up.divide(common);
            down = down.divide(common);
        }
        return down.equals(BigInteger.ONE) ? up.toString() : up + "/" + down;
    }
}
