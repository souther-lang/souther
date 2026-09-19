package souther.compiler.numeric;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.List;

/**
 * An exact ratio of two whole numbers, which is what the constraint algebra reasons in.
 *
 * <p>Not a number a model writes, and not a count a carrier is on. A model's decimals are finite
 * decimals and a carrier's counts are whatever it counts to; both are {@link BigDecimal} and both
 * are closed under adding and multiplying. Dividing is what neither of them is closed under, and
 * dividing is what deriving a bound does: {@code 3 * a <= 1} puts {@code a} at a third, and a third
 * is not a decimal anybody can write. Held as a {@code BigDecimal} the third has to be rounded at
 * the moment it is derived, and every later step reasons about the rounded number instead — so the
 * algebra decides feasibility, entailment and refutation on a value that is not the one the rules
 * put there.
 *
 * <p>So the algebra keeps ratios and rounds once, at the edge where a bound becomes something a
 * reader can be handed. What is exact stays exact for as long as it is being reasoned about.
 *
 * <p>Deliberately not a {@link Place}. A place is where a range stops on a carrier's order, and
 * every carrier's order is counted in decimals; a ratio is a step in the reasoning that produces
 * one. Keeping them separate types is what stops a third reaching a row.
 *
 * <p><b>The value is</b>
 *
 * <pre>{@code
 * numeratorWithoutUnits / denominatorWithoutUnits × 2^twos × 5^fives
 * }</pre>
 *
 * <p><b>Why two and five stand apart from the fraction.</b> A decimal is an unscaled whole number
 * over a power of ten, and its scale is four bytes. Written as a plain fraction, embedding that
 * decimal means building {@code 10^scale} — a value compact where a model wrote it becoming work
 * proportional to its scale by nothing more than entering this algebra, and every operation after it
 * carrying the wide denominator along. So the factors ten is made of are held as exponents, and a
 * decimal is taken in by two subtractions. Ten alone is not enough: a single power of ten cannot
 * hold a half, whose only factor is a two, and the two exponents of a sixth are not equal. What is
 * left over — a third's three — stays in the fraction.
 *
 * <p><b>One representation per value.</b> Every non-zero ratio is uniquely
 * {@code n/d · 2^a · 5^b} where {@code n} and {@code d} are coprime, {@code d} is positive and
 * neither is divisible by two or by five. So {@link #equals} decides equality of value, and a
 * canonical form built out of these is compared by its map.
 *
 * <p><b>Why the exponents are sixty-four bits.</b> A decimal's scale is thirty-two bits and enters
 * as its negation, and negating the least thirty-two-bit number leaves it — so an exponent held to a
 * scale's own width would refuse a decimal this type exists to take exactly.
 *
 * <p>The two numbers past the exponents are not the fraction the value is, and no caller should read
 * them as one. {@link #asFraction} is where a caller asks for that, and it costs what writing the
 * powers out costs.
 */
public record ExactRatio(BigInteger numeratorWithoutUnits, BigInteger denominatorWithoutUnits,
        long twos, long fives) implements Comparable<ExactRatio> {

    /** Declared before the two values below, which are built by a constructor that reads it. */
    private static final BigInteger FIVE = BigInteger.valueOf(5);

    public static final ExactRatio ZERO = new ExactRatio(BigInteger.ZERO, BigInteger.ONE, 0, 0);
    public static final ExactRatio ONE = new ExactRatio(BigInteger.ONE, BigInteger.ONE, 0, 0);

    /** How close in bits two magnitudes have to stand before the order is decided by writing both
     *  of them out. Past this the bit lengths of the stored fractions and the exponents separate the
     *  pair on their own, which is the case the exponents exist for. */
    private static final double APART = 4.0;

    /** {@code log2(5)} rounded down, with {@link #APART} covering what the rounding leaves. */
    private static final double LOG2_OF_FIVE = 2.321928094887362;

    public ExactRatio {
        if (numeratorWithoutUnits == null || denominatorWithoutUnits == null) {
            throw new IllegalArgumentException("a ratio is two whole numbers");
        }
        if (denominatorWithoutUnits.signum() == 0) {
            throw new IllegalArgumentException(
                    "a ratio has no zero denominator: " + numeratorWithoutUnits + "/0");
        }
        if (numeratorWithoutUnits.signum() == 0) {
            denominatorWithoutUnits = BigInteger.ONE;
            twos = 0;
            fives = 0;
        } else {
            if (denominatorWithoutUnits.signum() < 0) {
                numeratorWithoutUnits = numeratorWithoutUnits.negate();
                denominatorWithoutUnits = denominatorWithoutUnits.negate();
            }
            BigInteger common = numeratorWithoutUnits.gcd(denominatorWithoutUnits);
            if (!common.equals(BigInteger.ONE)) {
                numeratorWithoutUnits = numeratorWithoutUnits.divide(common);
                denominatorWithoutUnits = denominatorWithoutUnits.divide(common);
            }
            for (BigInteger unit : List.of(BigInteger.TWO, FIVE)) {
                long moved = 0;
                while (numeratorWithoutUnits.mod(unit).signum() == 0) {
                    numeratorWithoutUnits = numeratorWithoutUnits.divide(unit);
                    moved++;
                }
                while (denominatorWithoutUnits.mod(unit).signum() == 0) {
                    denominatorWithoutUnits = denominatorWithoutUnits.divide(unit);
                    moved--;
                }
                if (unit.equals(BigInteger.TWO)) {
                    twos = added(twos, moved);
                } else {
                    fives = added(fives, moved);
                }
            }
        }
    }

    /** A plain fraction, which is one with no power of two or five taken out of it yet. */
    public ExactRatio(BigInteger numerator, BigInteger denominator) {
        this(numerator, denominator, 0, 0);
    }

    public static ExactRatio of(long whole) {
        return new ExactRatio(BigInteger.valueOf(whole), BigInteger.ONE);
    }

    public static ExactRatio of(BigInteger whole) {
        return new ExactRatio(whole, BigInteger.ONE);
    }

    public static ExactRatio of(BigInteger numerator, BigInteger denominator) {
        return new ExactRatio(numerator, denominator);
    }

    /**
     * The ratio a written decimal is, exactly.
     *
     * <p>Every finite decimal is one, which is the direction that never loses anything: a decimal
     * with scale {@code s} is its unscaled value times {@code 2^-s · 5^-s}, so the scale moves into
     * the exponents and nothing is built. A negative scale is a decimal written as a multiple of a
     * power of ten, and the same two exponents hold it — the whole number it denotes has as many
     * digits as it has, and this holds the value it was given without spelling them.
     */
    public static ExactRatio of(BigDecimal at) {
        long scale = at.scale();
        return new ExactRatio(at.unscaledValue(), BigInteger.ONE, -scale, -scale);
    }

    /**
     * This as the one fraction it is, with the powers of two and five written into the two numbers.
     *
     * <p>For a caller whose question is about those numbers themselves — a modular inverse, a
     * remainder, a pair of numbers a reader is shown. It costs what the exponents say, which is why
     * nothing here reaches for it to do arithmetic.
     */
    public Fraction asFraction() {
        return new Fraction(
                numeratorWithoutUnits.multiply(power(BigInteger.TWO, Math.max(twos, 0)))
                        .multiply(power(FIVE, Math.max(fives, 0))),
                denominatorWithoutUnits.multiply(power(BigInteger.TWO, Math.max(-twos, 0)))
                        .multiply(power(FIVE, Math.max(-fives, 0))));
    }

    /** A ratio with its powers of two and five spelled out: two whole numbers in lowest terms, the
     *  second of them positive. */
    public record Fraction(BigInteger numerator, BigInteger denominator) {}

    public ExactRatio plus(ExactRatio other) {
        if (isZero()) {
            return other;
        }
        if (other.isZero()) {
            return this;
        }
        // The shared powers come out in front, and what is left of each side's exponents is written
        // into its numerator. That difference is the sum's own size: a millionth added to one has a
        // million digits whatever holds it.
        long sharedTwos = Math.min(twos, other.twos);
        long sharedFives = Math.min(fives, other.fives);
        BigInteger mine = numeratorWithoutUnits
                .multiply(power(BigInteger.TWO, twos - sharedTwos))
                .multiply(power(FIVE, fives - sharedFives));
        BigInteger theirs = other.numeratorWithoutUnits
                .multiply(power(BigInteger.TWO, other.twos - sharedTwos))
                .multiply(power(FIVE, other.fives - sharedFives));
        return new ExactRatio(
                mine.multiply(other.denominatorWithoutUnits)
                        .add(theirs.multiply(denominatorWithoutUnits)),
                denominatorWithoutUnits.multiply(other.denominatorWithoutUnits),
                sharedTwos, sharedFives);
    }

    public ExactRatio minus(ExactRatio other) {
        return plus(other.negated());
    }

    public ExactRatio times(ExactRatio other) {
        return new ExactRatio(numeratorWithoutUnits.multiply(other.numeratorWithoutUnits),
                denominatorWithoutUnits.multiply(other.denominatorWithoutUnits),
                added(twos, other.twos), added(fives, other.fives));
    }

    /** This over {@code other}.
     *
     *  @throws ArithmeticException where {@code other} is zero, which is a caller's mistake and not
     *          a value this can hold */
    public ExactRatio dividedBy(ExactRatio other) {
        if (other.signum() == 0) {
            throw new ArithmeticException("divided by zero");
        }
        return new ExactRatio(numeratorWithoutUnits.multiply(other.denominatorWithoutUnits),
                denominatorWithoutUnits.multiply(other.numeratorWithoutUnits),
                added(twos, -other.twos), added(fives, -other.fives));
    }

    public ExactRatio negated() {
        return new ExactRatio(numeratorWithoutUnits.negate(), denominatorWithoutUnits, twos, fives);
    }

    public ExactRatio abs() {
        return signum() < 0 ? negated() : this;
    }

    public int signum() {
        return numeratorWithoutUnits.signum();
    }

    public boolean isZero() {
        return numeratorWithoutUnits.signum() == 0;
    }

    /** Whether this is a whole number, which is a fraction of one with no power below the line. */
    public boolean isWhole() {
        return isZero()
                || denominatorWithoutUnits.equals(BigInteger.ONE) && twos >= 0 && fives >= 0;
    }

    /**
     * The part of the denominator a finite decimal cannot divide by, which is one exactly where this
     * value is a finite decimal.
     *
     * <p>What a caller doing arithmetic modulo the spread of a coefficient is asking for. Two and
     * five are units among the finite decimals, so what decides how far apart the members of an
     * image stand is the denominator with both taken out — and this holds that number rather than
     * having to find it.
     */
    public BigInteger spread() {
        return denominatorWithoutUnits;
    }

    @Override
    public int compareTo(ExactRatio other) {
        if (signum() != other.signum()) {
            return Integer.compare(signum(), other.signum());
        }
        if (isZero()) {
            return 0;
        }
        int bracketed = bracket(other);
        if (bracketed != 0) {
            return signum() < 0 ? -bracketed : bracketed;
        }
        // The bracket did not separate them, so the exponents stand within a few bits of each other
        // and writing the difference down costs about what the two fractions cost.
        long sharedTwos = Math.min(twos, other.twos);
        long sharedFives = Math.min(fives, other.fives);
        BigInteger mine = numeratorWithoutUnits
                .multiply(power(BigInteger.TWO, twos - sharedTwos))
                .multiply(power(FIVE, fives - sharedFives))
                .multiply(other.denominatorWithoutUnits);
        BigInteger theirs = other.numeratorWithoutUnits
                .multiply(power(BigInteger.TWO, other.twos - sharedTwos))
                .multiply(power(FIVE, other.fives - sharedFives))
                .multiply(denominatorWithoutUnits);
        return mine.compareTo(theirs);
    }

    /**
     * Which of two magnitudes is the larger where their bit lengths say so, and zero where they
     * stand too close for that to settle it.
     *
     * <p>Exact in what it answers: the fraction each side holds is bracketed by its bit lengths to
     * within a bit, and the powers are exact counts of bits, so a gap wider than that bracket is a
     * gap. It says nothing about the pairs it leaves at zero, which are the ones written out.
     */
    private int bracket(ExactRatio other) {
        double fractions = numeratorWithoutUnits.abs().bitLength()
                - denominatorWithoutUnits.bitLength()
                - (other.numeratorWithoutUnits.abs().bitLength()
                        - other.denominatorWithoutUnits.bitLength());
        double powers = (double) (twos - other.twos)
                + (double) (fives - other.fives) * LOG2_OF_FIVE;
        double gap = fractions + powers;
        if (gap > APART) {
            return 1;
        }
        return gap < -APART ? -1 : 0;
    }

    /** The largest whole number no greater than this. */
    public BigInteger floor() {
        Fraction fraction = asFraction();
        BigInteger[] parts = fraction.numerator().divideAndRemainder(fraction.denominator());
        return parts[1].signum() < 0 ? parts[0].subtract(BigInteger.ONE) : parts[0];
    }

    /** The smallest whole number no less than this. */
    public BigInteger ceiling() {
        Fraction fraction = asFraction();
        BigInteger[] parts = fraction.numerator().divideAndRemainder(fraction.denominator());
        return parts[1].signum() > 0 ? parts[0].add(BigInteger.ONE) : parts[0];
    }

    /** This with the part of it past the point dropped, which is towards nought from either side. */
    public BigInteger truncated() {
        Fraction fraction = asFraction();
        return fraction.numerator().divide(fraction.denominator());
    }

    /**
     * The greatest common divisor of two ratios: the largest {@code g} of which both are whole
     * multiples.
     *
     * <p>What generates the values a form's coefficients reach. In lowest terms it is
     * {@code gcd(numerators) / lcm(denominators)} — a third and a half are both whole multiples of a
     * sixth and of nothing larger. Held this way each factor is asked separately: the power of two
     * both are multiples of is the smaller of the two, and so is the power of five. Zero divides
     * nothing and is divided by everything, so it is the identity here: a coefficient that is zero is
     * a position the form does not name.
     */
    public static ExactRatio gcd(ExactRatio a, ExactRatio b) {
        if (a.isZero()) {
            return b.abs();
        }
        if (b.isZero()) {
            return a.abs();
        }
        BigInteger tops = a.numeratorWithoutUnits.abs().gcd(b.numeratorWithoutUnits.abs());
        BigInteger common = a.denominatorWithoutUnits.gcd(b.denominatorWithoutUnits);
        BigInteger bottoms = a.denominatorWithoutUnits.divide(common)
                .multiply(b.denominatorWithoutUnits);
        return new ExactRatio(tops, bottoms, Math.min(a.twos, b.twos), Math.min(a.fives, b.fives));
    }

    /**
     * This as a decimal a model could write, or {@code null} where no such decimal is this.
     *
     * <p>A ratio terminates exactly where its denominator is made of the factors ten is made of,
     * which here is where nothing is left below the line once both of them are held as exponents. A
     * third does not, and answering that with a rounded decimal is what this exists to stop: the
     * caller asking has to know whether it was handed the value or an approximation of it, and a
     * number that came back cannot be asked which it was.
     *
     * @throws ArithmeticException where the decimal this is has a scale no {@link BigDecimal} holds,
     *         which is a value with no written form rather than a value that is not one
     */
    public BigDecimal asWrittenDecimal() {
        if (isZero()) {
            return BigDecimal.ZERO;
        }
        if (!denominatorWithoutUnits.equals(BigInteger.ONE)) {
            return null;
        }
        // Ten carries one two and one five, so the tens it takes is however many of the more
        // negative of them this stands on, and neither exponent is below the line after that.
        long scale = Math.max(0, Math.max(-twos, -fives));
        if (scale > Integer.MAX_VALUE) {
            throw new ArithmeticException("no decimal holds a scale of " + scale);
        }
        return new BigDecimal(
                numeratorWithoutUnits.multiply(power(BigInteger.TWO, twos + scale))
                        .multiply(power(FIVE, fives + scale)),
                (int) scale);
    }

    /**
     * This with the factors a finite decimal can be divided by taken out of it.
     *
     * <p>Ten is a unit among the finite decimals, so two and five are: dividing by either lands on a
     * finite decimal again, above and below the line alike. Taking them out is what makes two
     * numbers that generate one set of decimals one value — a quarter and a tenth both generate
     * every decimal there is, and so does one. Held this way they are already out, and this is the
     * fraction that was left.
     *
     * <p><b>Total, and the two ends of it say why.</b> One below zero is a unit as well, so what
     * comes back is never negative: three and minus three generate the same decimals. And nothing
     * divides into zero, or rather everything does — taking a factor out of it leaves it where it
     * was.
     */
    public ExactRatio unitsRemoved() {
        if (isZero()) {
            return ZERO;
        }
        return new ExactRatio(numeratorWithoutUnits.abs(), denominatorWithoutUnits, 0, 0);
    }

    /**
     * This as a decimal, rounded the way {@code towards} says where it is not one exactly.
     *
     * <p>For a bound that has to be handed over as a written number. The direction is the caller's
     * because only the caller knows which way widens: an upper bound rounded up still admits
     * everything the rules admit, and rounded down refuses values they leave.
     */
    public BigDecimal asDecimal(RoundingMode towards, int scale) {
        Fraction fraction = asFraction();
        return new BigDecimal(fraction.numerator())
                .divide(new BigDecimal(fraction.denominator()), scale, towards);
    }

    /**
     * This as a reader is shown it: the decimal where one is this exactly, and the quotient of two
     * whole numbers where none is.
     *
     * <p>The decimal first because that is what a model writes, and what every number reaching a
     * report was until an exact scalar could hold something else. A coefficient of a half spelled
     * {@code 1/2} in a document that used to say {@code 0.5} is a report changed by a
     * representation, which is not a difference anybody asked for. A third has no decimal, and
     * saying {@code 1/3} is the honest answer where rounding one would not be.
     *
     * <p>Apart from {@link #toString}, which is for a message about this compiler and says the plain
     * shape of the number. This is for a sentence somebody reads about their own model.
     */
    public String spelled() {
        BigDecimal written = asWrittenDecimal();
        if (written != null) {
            return written.stripTrailingZeros().toPlainString();
        }
        Fraction fraction = asFraction();
        return fraction.numerator() + "/" + fraction.denominator();
    }

    @Override
    public String toString() {
        if (isWhole()) {
            return asFraction().numerator().toString();
        }
        Fraction fraction = asFraction();
        return fraction.numerator() + "/" + fraction.denominator();
    }

    /** {@code base^exponent}, where the exponent is one this type holds and the power is one the
     *  host builds. */
    private static BigInteger power(BigInteger base, long exponent) {
        if (exponent == 0) {
            return BigInteger.ONE;
        }
        if (exponent > Integer.MAX_VALUE) {
            throw new ArithmeticException("no whole number is " + base + " to the " + exponent);
        }
        return base.pow((int) exponent);
    }

    /** Two exponents added, where a sum past this width is a value with no representation here. */
    private static long added(long one, long other) {
        try {
            return Math.addExact(one, other);
        } catch (ArithmeticException _) {
            throw new ArithmeticException(
                    "no ratio here stands at two to the " + one + " times two to the " + other);
        }
    }
}
