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
            within(twos);
            within(fives);
        }
    }

    /**
     * An exponent this type holds, which is one whose negation it holds too.
     *
     * <p>Asked here because here is where every ratio is made, and because the rule it keeps is the
     * one every other method would otherwise have to ask for itself. Taking a reciprocal negates
     * both exponents, reading the scale of the decimal this is negates them, and writing the powers
     * out puts whichever of them is below the line on the other side of it — so a value at an
     * exponent whose negation is not held is a value no operation here can act on. The least number
     * a long holds is its own negation, and so it is the one exponent that is not one of these: a
     * value that reached it has left what this can represent, which is said where it happens rather
     * than at whichever method next tries to turn it round.
     */
    private static void within(long exponent) {
        if (exponent == Long.MIN_VALUE) {
            throw new ArithmeticException("no ratio here stands at an exponent of " + exponent);
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
     * <p><b>The digits, and only for somewhere that needs the digits</b> — a number printed in a
     * sentence, a whole number handed to something that counts in whole numbers. It costs what the
     * exponents say, which is the cost this type is held the way it is to avoid, so reaching for it
     * is reaching past the representation.
     *
     * <p>Everything a reasoning step asks of the two numbers is asked of this type instead:
     * {@link #numeratorMod} and {@link #denominatorMod} for a residue, {@link #numeratorAsRatio} and
     * {@link #denominatorAsRatio} for either of them as a value to go on computing with,
     * {@link #spread} for the part of the denominator no finite decimal divides. Each of those
     * answers from the factors and builds nothing.
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

    /** The number above this ratio's line, as a ratio — so that a caller going on to compute with it
     *  is handed the factors rather than the digits. */
    public ExactRatio numeratorAsRatio() {
        return new ExactRatio(numeratorWithoutUnits, BigInteger.ONE,
                Math.max(twos, 0), Math.max(fives, 0));
    }

    /** What this ratio stands over, as a ratio. */
    public ExactRatio denominatorAsRatio() {
        return new ExactRatio(denominatorWithoutUnits, BigInteger.ONE,
                Math.max(-twos, 0), Math.max(-fives, 0));
    }

    /**
     * This ratio's numerator modulo {@code modulus}, which is what a congruence asks of it.
     *
     * <p>A residue is all such a caller wants, and a residue of a power is reached by the bits of
     * its exponent — so the number the residue is of is never formed. A step that asked for the
     * fraction first would have spent the whole of what the representation saves to throw away all
     * but a few digits of it.
     *
     * @param modulus a positive whole number
     */
    public BigInteger numeratorMod(BigInteger modulus) {
        return residue(numeratorWithoutUnits, Math.max(twos, 0), Math.max(fives, 0), modulus);
    }

    /** What this ratio stands over, modulo {@code modulus}.
     *
     *  @param modulus a positive whole number */
    public BigInteger denominatorMod(BigInteger modulus) {
        return residue(denominatorWithoutUnits, Math.max(-twos, 0), Math.max(-fives, 0), modulus);
    }

    private static BigInteger residue(BigInteger of, long twos, long fives, BigInteger modulus) {
        return of.mod(modulus)
                .multiply(BigInteger.TWO.modPow(BigInteger.valueOf(twos), modulus))
                .multiply(FIVE.modPow(BigInteger.valueOf(fives), modulus))
                .mod(modulus);
    }

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
        return new ExactRatio(
                numeratorOver(sharedTwos, sharedFives).multiply(other.denominatorWithoutUnits)
                        .add(other.numeratorOver(sharedTwos, sharedFives)
                                .multiply(denominatorWithoutUnits)),
                denominatorWithoutUnits.multiply(other.denominatorWithoutUnits),
                sharedTwos, sharedFives);
    }

    /**
     * This ratio's numerator once the powers it stands above {@code sharedTwos} and
     * {@code sharedFives} are written into it, which is what a sum and an order both need of both
     * sides before either can be formed over one denominator.
     *
     * <p>The two exponents are no lower than this ratio's own, because what they are is the lower of
     * two ratios' — so nothing here is a power below the line.
     */
    private BigInteger numeratorOver(long sharedTwos, long sharedFives) {
        return numeratorWithoutUnits
                .multiply(power(BigInteger.TWO, lessened(twos, sharedTwos)))
                .multiply(power(FIVE, lessened(fives, sharedFives)));
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
                lessened(twos, other.twos), lessened(fives, other.fives));
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
                || (denominatorWithoutUnits.equals(BigInteger.ONE) && twos >= 0 && fives >= 0);
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

    /**
     * Where this stands against {@code other}, by writing both sides over one denominator.
     *
     * <p>No reading short of that, and the reason is what this type is. A power of five is not a
     * count of bits, so anything cheaper rests on how well a whole number stands against the log of
     * five — and the exponents here run to the width of a long, so the error in such a reading grows
     * with the exponent and no margin settled on beforehand bounds it. A reading that is not a proof
     * can put two values in the wrong order, and an order this type got wrong is a bound the algebra
     * then reasons from.
     *
     * <p>So the cost of this is the cost of the difference between the two sides' powers, which is
     * what the difference between the two values is. A cheaper order exists and is a real thing to
     * want — a pair set far apart by its exponents is settled by brackets taken again wider until
     * they come apart, which is what {@code Rational} does at run time. A second copy of that
     * mechanism is the thing not to have: one of the two would be the one that drifts. Shared or not
     * at all.
     *
     * <p>Which leaves a pair whose powers stand further apart than a whole number this host builds:
     * the order between those two exists and this cannot reach it, and that is said rather than
     * guessed at. A reading that answered such a pair from a machine's fractions would be answering
     * exactly where it has no proof.
     *
     * @throws ArithmeticException where the difference between the two sides' powers is past what a
     *         whole number here holds
     */
    @Override
    public int compareTo(ExactRatio other) {
        if (signum() != other.signum()) {
            return Integer.compare(signum(), other.signum());
        }
        if (isZero()) {
            return 0;
        }
        long sharedTwos = Math.min(twos, other.twos);
        long sharedFives = Math.min(fives, other.fives);
        return numeratorOver(sharedTwos, sharedFives).multiply(other.denominatorWithoutUnits)
                .compareTo(other.numeratorOver(sharedTwos, sharedFives)
                        .multiply(denominatorWithoutUnits));
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
     * Whether a decimal is this exactly, which is a question about the value and not about any
     * decimal that would hold it.
     *
     * <p>Separate from {@link #asWrittenDecimal} because a step asking only this is asking something
     * the denominator answers on its own, and going through the number would make the answer depend
     * on whether a {@link BigDecimal} has room for it — so a value that is a decimal, written at a
     * scale past what a scale holds, would come back as one that is not. Which of those two a caller
     * wants is not a distinction to leave to a null.
     */
    public boolean terminates() {
        return isZero() || denominatorWithoutUnits.equals(BigInteger.ONE);
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
                numeratorWithoutUnits.multiply(power(BigInteger.TWO, added(twos, scale)))
                        .multiply(power(FIVE, added(fives, scale))),
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

    /**
     * The plain shape of the number, for a message about this compiler.
     *
     * <p>The fraction and not what is held, because the number is what a reader of such a message
     * needs. Writing it is what writing a number costs, which for a value held compactly is more
     * than holding it — so this is not somewhere to reach for on a path that has to stay cheap.
     */
    @Override
    public String toString() {
        Fraction fraction = asFraction();
        return isWhole() ? fraction.numerator().toString()
                : fraction.numerator() + "/" + fraction.denominator();
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
            throw beyond(one, other);
        }
    }

    /** One exponent less another, which every pair of these is asked for somewhere: a quotient
     *  subtracts them, and what an operand stands above the lower of the two is what a sum and an
     *  order write down. */
    private static long lessened(long one, long other) {
        try {
            return Math.subtractExact(one, other);
        } catch (ArithmeticException _) {
            throw beyond(one, other);
        }
    }

    private static ArithmeticException beyond(long one, long other) {
        return new ArithmeticException(
                "no ratio here stands between an exponent of " + one + " and one of " + other);
    }
}
