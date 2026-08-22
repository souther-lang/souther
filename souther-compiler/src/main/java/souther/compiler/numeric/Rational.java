package souther.compiler.numeric;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;

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
 * <p>Always in lowest terms with a positive denominator, so two ratios of equal value are one value
 * — {@link #equals} decides it, and a canonical form built out of these is compared by its map.
 */
public record Rational(BigInteger numerator, BigInteger denominator) implements Comparable<Rational> {

    public static final Rational ZERO = new Rational(BigInteger.ZERO, BigInteger.ONE);
    public static final Rational ONE = new Rational(BigInteger.ONE, BigInteger.ONE);

    private static final BigInteger FIVE = BigInteger.valueOf(5);

    public Rational {
        if (numerator == null || denominator == null) {
            throw new IllegalArgumentException("a ratio is two whole numbers");
        }
        if (denominator.signum() == 0) {
            throw new IllegalArgumentException("a ratio has no zero denominator: " + numerator + "/0");
        }
        if (denominator.signum() < 0) {
            numerator = numerator.negate();
            denominator = denominator.negate();
        }
        BigInteger common = numerator.gcd(denominator);
        if (!common.equals(BigInteger.ONE)) {
            numerator = numerator.divide(common);
            denominator = denominator.divide(common);
        }
    }

    public static Rational of(long whole) {
        return new Rational(BigInteger.valueOf(whole), BigInteger.ONE);
    }

    public static Rational of(BigInteger whole) {
        return new Rational(whole, BigInteger.ONE);
    }

    public static Rational of(BigInteger numerator, BigInteger denominator) {
        return new Rational(numerator, denominator);
    }

    /**
     * The ratio a written decimal is, exactly.
     *
     * <p>Every finite decimal is one, which is the direction that never loses anything: a decimal
     * with scale {@code s} is its unscaled value over {@code 10^s}. A negative scale is a decimal
     * written as a multiple of a power of ten and is a whole number.
     */
    public static Rational of(BigDecimal at) {
        BigInteger unscaled = at.unscaledValue();
        int scale = at.scale();
        return scale >= 0
                ? new Rational(unscaled, BigInteger.TEN.pow(scale))
                : new Rational(unscaled.multiply(BigInteger.TEN.pow(-scale)), BigInteger.ONE);
    }

    public Rational plus(Rational other) {
        return new Rational(
                numerator.multiply(other.denominator).add(other.numerator.multiply(denominator)),
                denominator.multiply(other.denominator));
    }

    public Rational minus(Rational other) {
        return plus(other.negated());
    }

    public Rational times(Rational other) {
        return new Rational(numerator.multiply(other.numerator),
                denominator.multiply(other.denominator));
    }

    /** @throws ArithmeticException where {@code other} is zero, which is a caller's mistake and not
     *  a value this can hold */
    public Rational dividedBy(Rational other) {
        if (other.signum() == 0) {
            throw new ArithmeticException("divided by zero");
        }
        return new Rational(numerator.multiply(other.denominator),
                denominator.multiply(other.numerator));
    }

    public Rational negated() {
        return new Rational(numerator.negate(), denominator);
    }

    public Rational abs() {
        return signum() < 0 ? negated() : this;
    }

    public int signum() {
        return numerator.signum();
    }

    public boolean isZero() {
        return numerator.signum() == 0;
    }

    /** Whether this is a whole number, which is what a denominator of one says. */
    public boolean isWhole() {
        return denominator.equals(BigInteger.ONE);
    }

    @Override
    public int compareTo(Rational other) {
        return numerator.multiply(other.denominator).compareTo(other.numerator.multiply(denominator));
    }

    /** The largest whole number no greater than this. */
    public BigInteger floor() {
        BigInteger[] parts = numerator.divideAndRemainder(denominator);
        return parts[1].signum() < 0 ? parts[0].subtract(BigInteger.ONE) : parts[0];
    }

    /** The smallest whole number no less than this. */
    public BigInteger ceiling() {
        BigInteger[] parts = numerator.divideAndRemainder(denominator);
        return parts[1].signum() > 0 ? parts[0].add(BigInteger.ONE) : parts[0];
    }

    /**
     * The greatest common divisor of two ratios: the largest {@code g} of which both are whole
     * multiples.
     *
     * <p>What generates the values a form's coefficients reach. In lowest terms it is
     * {@code gcd(numerators) / lcm(denominators)} — a third and a half are both whole multiples of a
     * sixth and of nothing larger. Zero divides nothing and is divided by everything, so it is the
     * identity here: a coefficient that is zero is a position the form does not name.
     */
    public static Rational gcd(Rational a, Rational b) {
        if (a.isZero()) {
            return b.abs();
        }
        if (b.isZero()) {
            return a.abs();
        }
        BigInteger tops = a.numerator.abs().gcd(b.numerator.abs());
        BigInteger common = a.denominator.gcd(b.denominator);
        BigInteger bottoms = a.denominator.divide(common).multiply(b.denominator);
        return new Rational(tops, bottoms);
    }

    /**
     * This as a decimal a model could write, or {@code null} where no such decimal is this.
     *
     * <p>A ratio terminates exactly where its denominator is made of the factors ten is made of. A
     * third does not, and answering that with a rounded decimal is what this exists to stop: the
     * caller asking has to know whether it was handed the value or an approximation of it, and a
     * number that came back cannot be asked which it was.
     */
    public BigDecimal asWrittenDecimal() {
        BigInteger left = denominator;
        int twos = 0;
        while (left.mod(BigInteger.TWO).signum() == 0) {
            left = left.divide(BigInteger.TWO);
            twos++;
        }
        int fives = 0;
        while (left.mod(FIVE).signum() == 0) {
            left = left.divide(FIVE);
            fives++;
        }
        if (!left.equals(BigInteger.ONE)) {
            return null;
        }
        // Ten carries one two and one five, so the tens it takes to clear the denominator is however
        // many of the more numerous of them it holds.
        int scale = Math.max(twos, fives);
        return new BigDecimal(
                numerator.multiply(BigInteger.TEN.pow(scale)).divide(denominator), scale);
    }

    /**
     * This with the factors a finite decimal can be divided by taken out of it.
     *
     * <p>Ten is a unit among the finite decimals, so two and five are: dividing by either lands on a
     * finite decimal again, above and below the line alike. Taking them out is what makes two
     * numbers that generate one set of decimals one value — a quarter and a tenth both generate
     * every decimal there is, and so does one.
     */
    public Rational unitsRemoved() {
        BigInteger top = numerator.abs();
        BigInteger bottom = denominator;
        for (BigInteger unit : java.util.List.of(BigInteger.TWO, FIVE)) {
            while (top.mod(unit).signum() == 0) {
                top = top.divide(unit);
            }
            while (bottom.mod(unit).signum() == 0) {
                bottom = bottom.divide(unit);
            }
        }
        return Rational.of(top, bottom);
    }

    /**
     * This as a decimal, rounded the way {@code towards} says where it is not one exactly.
     *
     * <p>For a bound that has to be handed over as a written number. The direction is the caller's
     * because only the caller knows which way widens: an upper bound rounded up still admits
     * everything the rules admit, and rounded down refuses values they leave.
     */
    public BigDecimal asDecimal(RoundingMode towards, int scale) {
        return new BigDecimal(numerator).divide(new BigDecimal(denominator), scale, towards);
    }

    @Override
    public String toString() {
        return isWhole() ? numerator.toString() : numerator + "/" + denominator;
    }
}
