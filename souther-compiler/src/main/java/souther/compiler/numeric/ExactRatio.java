package souther.compiler.numeric;

import souther.exact.ExactArithmetic;
import souther.exact.ExactParts;

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
 * <p><b>The value is</b>
 *
 * <pre>{@code
 * numeratorWithoutUnits / denominatorWithoutUnits × 2^twos × 5^fives
 * }</pre>
 *
 * <p>Two and five stand apart from the fraction so that a decimal is taken in by two subtractions and
 * not by building {@code 10^scale}, and every non-zero ratio has one representation, so {@link #equals}
 * decides equality of value and a canonical form built out of these is compared by its map. The
 * arithmetic on that representation is {@link ExactArithmetic}'s, which the run time's own rationals
 * use as well: this is a different type with the same mathematics, and what it says of a failure is an
 * {@link ArithmeticException}, which is what one is.
 *
 * <p><b>Why the exponents are sixty-four bits, and all of them.</b> A decimal's scale is thirty-two bits
 * and enters as its negation, and negating the least thirty-two-bit number leaves it — so an exponent
 * held to a scale's own width would refuse a decimal this type exists to take exactly. And the least
 * sixty-four-bit exponent is a value like any other: that a value is held does not mean its negation is,
 * so what needs a negation is what refuses, and it refuses for the answer and not for the value.
 *
 * <p>The two numbers past the exponents are not the fraction the value is, and no caller should read
 * them as one. {@link #asFraction} is where a caller asks for that, and it costs what writing the
 * powers out costs.
 */
public record ExactRatio(BigInteger numeratorWithoutUnits, BigInteger denominatorWithoutUnits,
        long twos, long fives) implements Comparable<ExactRatio> {

    private static final BigInteger FIVE = BigInteger.valueOf(5);

    public static final ExactRatio ZERO = new ExactRatio(BigInteger.ZERO, BigInteger.ONE, 0, 0);
    public static final ExactRatio ONE = new ExactRatio(BigInteger.ONE, BigInteger.ONE, 0, 0);

    public ExactRatio {
        ExactParts canonical = ExactArithmetic.canonical(
                numeratorWithoutUnits, denominatorWithoutUnits, twos, fives);
        numeratorWithoutUnits = canonical.numerator();
        denominatorWithoutUnits = canonical.denominator();
        twos = canonical.twos();
        fives = canonical.fives();
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

    private ExactParts parts() {
        return new ExactParts(numeratorWithoutUnits, denominatorWithoutUnits, twos, fives);
    }

    private static ExactRatio from(ExactParts parts) {
        return new ExactRatio(parts.numerator(), parts.denominator(), parts.twos(), parts.fives());
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
                ExactArithmetic.written(numeratorWithoutUnits,
                        ExactArithmetic.aboveTheLine(twos), ExactArithmetic.aboveTheLine(fives)),
                ExactArithmetic.written(denominatorWithoutUnits,
                        ExactArithmetic.belowTheLine(twos), ExactArithmetic.belowTheLine(fives)));
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

    /**
     * What this ratio stands over, as a ratio.
     *
     * @throws ArithmeticException where an exponent is the least long, whose negation is no exponent
     */
    public ExactRatio denominatorAsRatio() {
        return new ExactRatio(denominatorWithoutUnits, BigInteger.ONE,
                twos >= 0 ? 0 : ExactArithmetic.negated(twos),
                fives >= 0 ? 0 : ExactArithmetic.negated(fives));
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
        return residue(numeratorWithoutUnits,
                ExactArithmetic.aboveTheLine(twos), ExactArithmetic.aboveTheLine(fives), modulus);
    }

    /** What this ratio stands over, modulo {@code modulus}.
     *
     *  @param modulus a positive whole number */
    public BigInteger denominatorMod(BigInteger modulus) {
        return residue(denominatorWithoutUnits,
                ExactArithmetic.belowTheLine(twos), ExactArithmetic.belowTheLine(fives), modulus);
    }

    private static BigInteger residue(
            BigInteger of, BigInteger twos, BigInteger fives, BigInteger modulus) {
        return of.mod(modulus)
                .multiply(BigInteger.TWO.modPow(twos, modulus))
                .multiply(FIVE.modPow(fives, modulus))
                .mod(modulus);
    }

    public ExactRatio plus(ExactRatio other) {
        return from(ExactArithmetic.plus(parts(), other.parts()));
    }

    public ExactRatio minus(ExactRatio other) {
        return plus(other.negated());
    }

    public ExactRatio times(ExactRatio other) {
        return from(ExactArithmetic.times(parts(), other.parts()));
    }

    /** This over {@code other}.
     *
     *  @throws ArithmeticException where {@code other} is zero, which is a caller's mistake and not
     *          a value this can hold */
    public ExactRatio dividedBy(ExactRatio other) {
        if (other.signum() == 0) {
            throw new ArithmeticException("divided by zero");
        }
        return from(ExactArithmetic.dividedBy(parts(), other.parts()));
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
     * Where this stands against {@code other}, by exact value.
     *
     * <p>An order always exists, so this answers every pair — including the ones whose powers no
     * machine writes down. Two of those are a decimal written at either end of the scale a model may
     * write, so it is not an end of the range nothing reaches. Cross-multiplying would write out the
     * difference between their exponents, which is why the order is read from brackets of a working
     * width and not from the numbers ({@link ExactArithmetic#compare}).
     */
    @Override
    public int compareTo(ExactRatio other) {
        return ExactArithmetic.compare(parts(), other.parts());
    }

    /**
     * The largest whole number no greater than this.
     *
     * <p>Read the way the order is read, and for the same reason. How large a value is and how large
     * the whole number below it is are two questions: two powers that all but cancel leave a value
     * of about one, whose floor is one digit and whose two numbers are hundreds of millions. A step
     * that worked the second out by writing the value down refused such a value over an answer that
     * was never going to be large.
     */
    public BigInteger floor() {
        return rounded(RoundingMode.FLOOR, 0);
    }

    /** The smallest whole number no less than this. */
    public BigInteger ceiling() {
        return rounded(RoundingMode.CEILING, 0);
    }

    /** This with the part of it past the point dropped, which is towards nought from either side. */
    public BigInteger truncated() {
        return rounded(RoundingMode.DOWN, 0);
    }

    /**
     * The whole number {@code this × 10^scale} comes to, rounded the way {@code towards} says.
     *
     * <p>The tens stay a count and never become a ratio. Made into one they would have had to fit
     * the exponents a ratio holds, and a value whose powers all but cancel sits well inside those
     * while either of its own exponents stands at the end of them — so a step on the way would have
     * refused a value and an answer both of which are small.
     */
    private BigInteger rounded(RoundingMode towards, int scale) {
        try {
            return ExactArithmetic.roundedTimesTenTo(parts(), scale, towards);
        } catch (IllegalArgumentException _) {
            throw new ArithmeticException(
                    "no whole number is this value, and none was to be chosen for it");
        }
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
     * Whether some decimal is this value exactly, which is a fact about the number and not about any
     * {@link BigDecimal}.
     *
     * <p>A third is not one; a millionth of a millionth is, however far a machine would have to
     * count to write it. What a carrier holds is the narrower question, and
     * {@link #fitsWrittenDecimal} is where that one is asked.
     */
    public boolean terminates() {
        return isZero() || denominatorWithoutUnits.equals(BigInteger.ONE);
    }

    /**
     * Whether a {@link BigDecimal} is this value exactly, which is what a position holding what a
     * model can write is asking.
     *
     * <p>Narrower than {@link #terminates} by the scale a decimal has, and the two are not the same
     * question: a scale is thirty-two bits, so a value that is a finite decimal can still be one no
     * decimal here holds. A carrier's counts are decimals, so a step choosing a value for a position
     * asks this one; a step reasoning about the finite decimals as a set asks the other.
     *
     * <p><b>A rule of this language and of nothing else.</b> How many digits the unscaled value then
     * has is a question for whatever holds it, and holds nothing about what a decimal is: a value
     * this calls a decimal on a machine with room is the same value on one without. A membership
     * answered partly from a machine's room is one that would have let a run short of memory report
     * that a set is empty, and every reader of this is deciding a membership.
     *
     * <p>Asked of the exponents rather than by building anything, so the answer costs nothing.
     */
    public boolean fitsWrittenDecimal() {
        return terminates() && (isZero() || leastScale() <= Integer.MAX_VALUE);
    }

    /**
     * The least scale this value can be written at: the tens it takes to leave neither exponent
     * below the line.
     *
     * <p>Every scale from here up writes it too, so this is what decides whether any does. It is a
     * question about the language's scale and about nothing else — how many digits the unscaled
     * value then has is what a host holds or does not, and is not what makes a value a decimal.
     *
     * <p>Saturating for the least exponent, whose negation is no long: a scale past what a decimal
     * has is past it by any amount, and this is only ever compared with where a decimal's scale ends.
     */
    private long leastScale() {
        return Math.max(saturatingNegation(twos), saturatingNegation(fives));
    }

    private static long saturatingNegation(long exponent) {
        return exponent == Long.MIN_VALUE ? Long.MAX_VALUE : -exponent;
    }

    /**
     * Which scale a {@link BigDecimal} of this value is written at, this value being one some scale
     * writes.
     *
     * <p>More than one does: every scale from {@link #leastScale} up. The one taken is the plain
     * one — nothing below the line, and a value standing above it on both written out as the whole
     * number it is — because that is the shape a reader of a count expects and the one the rest of
     * this compiler was written against.
     *
     * <p>Where those digits are past what a whole number here holds, the plain shape is not on offer
     * and the scale goes below nought instead, which leaves the unscaled value only what the two
     * exponents differ by. A decimal written at the least scale one has is the case: its value is a
     * whole number of hundreds of millions of digits, and the decimal it came from held it in one.
     *
     * <p>Which of the two is a question about room and not about what a decimal is, so it decides
     * how the value is written and never whether it is one. A scale past the last one a decimal has
     * is what settles that, and {@link #fitsWrittenDecimal} is where it is settled.
     */
    private long scaleOfTheDecimal() {
        long least = leastScale();
        long plain = Math.max(0, least);
        return heldAt(plain) ? plain : Math.max(least, Integer.MIN_VALUE);
    }

    /**
     * Whether this value is written at {@code scale}: a scale a decimal has, and an unscaled value
     * this host holds.
     *
     * <p>Asked of how many bits that value takes rather than of the exponents alone. The two exponents
     * are added as whole numbers because a scale added to an exponent at the end of its range is a
     * sum no long holds — and a sum that wrapped would have picked a scale and then written a
     * different number at it.
     */
    private boolean heldAt(long scale) {
        if (scale < Integer.MIN_VALUE || scale > Integer.MAX_VALUE) {
            return false;
        }
        BigInteger byTwos = byTwosAt(scale);
        BigInteger byFives = byFivesAt(scale);
        if (byTwos.signum() < 0 || byFives.signum() < 0) {
            return false;
        }
        return ExactArithmetic.canBeWritten(numeratorWithoutUnits, byTwos, byFives);
    }

    /** How many twos the unscaled value at {@code scale} carries, as a whole number, since the sum
     *  is one a long need not hold. */
    private BigInteger byTwosAt(long scale) {
        return BigInteger.valueOf(twos).add(BigInteger.valueOf(scale));
    }

    private BigInteger byFivesAt(long scale) {
        return BigInteger.valueOf(fives).add(BigInteger.valueOf(scale));
    }

    /**
     * This as a decimal a model could write, or {@code null} where the caller cannot have one.
     *
     * <p>A ratio terminates exactly where its denominator is made of the factors ten is made of,
     * which here is where nothing is left below the line once both of them are held as exponents. A
     * third does not, and answering that with a rounded decimal is what this exists to stop: the
     * caller asking has to know whether it was handed the value or an approximation of it, and a
     * number that came back cannot be asked which it was.
     *
     * <p><b>And {@code null} for a value past the scale a decimal has</b>, which is the other way a
     * value is not one: both are rules of the language, both are settled by
     * {@link #fitsWrittenDecimal}, and a reader branching on the null is answering the question it
     * thinks it is.
     *
     * <p><b>What does not come back as {@code null} is a shortage of room.</b> A value this says is
     * a decimal, written at a scale this language has, whose digits are more than a whole number
     * this host addresses, leaves as a failure of the run. Handed back as a {@code null} it would
     * have become the answer that no decimal is this value — and then a coset would have said it
     * holds nothing, a bound that no value stands at it, and a search that a position has nowhere to
     * go. What a machine ran out of is not what a set contains.
     *
     * @throws ArithmeticException where the digits are past what a whole number here holds
     */
    public BigDecimal asWrittenDecimal() {
        if (isZero()) {
            return BigDecimal.ZERO;
        }
        if (!denominatorWithoutUnits.equals(BigInteger.ONE)) {
            return null;
        }
        if (!fitsWrittenDecimal()) {
            return null;
        }
        long scale = scaleOfTheDecimal();
        return new BigDecimal(
                ExactArithmetic.written(numeratorWithoutUnits, byTwosAt(scale), byFivesAt(scale)),
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
     *
     * <p>A decimal at a scale is a whole number of those places, so this is the rounding above with
     * the value moved by that many tens first — which moves two exponents and builds nothing. The
     * number that comes back is as large as the answer and no larger: neither the value's own two
     * numbers nor the power that carried it to the place is formed.
     */
    public BigDecimal asDecimal(RoundingMode towards, int scale) {
        return new BigDecimal(rounded(towards, scale), scale);
    }

    /**
     * This value named the one way it is named, for somewhere that has to tell two of them apart.
     *
     * <p>Not a number anybody reads — {@link #spelled} is that — and so not the digits. One
     * canonical form per value makes the four parts a name already: two values with the same name
     * are the same value, and the same value has the same name however it arrived. Written as a
     * fraction instead, a name is as long as the powers, and naming a line on a quantity is not a
     * reason to spell a millionth out.
     */
    public String key() {
        return numeratorWithoutUnits + "/" + denominatorWithoutUnits + ";" + twos + ";" + fives;
    }

    /**
     * The fewest places a decimal needs before the last of them lands inside this value: the least
     * count above nought with this value standing above ten to the minus that.
     *
     * <p>For a search that has to name a number inside a distance and wants to know how far in to
     * look. The count is what the value's size says, so it is read off the order rather than by
     * forming one over the value and counting its digits — a distance of a millionth has an answer
     * of about a million, and a number of that many digits built to be measured is the work this
     * type is held the way it is to avoid.
     *
     * @throws ArithmeticException where this value is at or below nought, which has no such count,
     *         or where the count is past what one here holds
     */
    public int placesItStandsAbove() {
        if (signum() <= 0) {
            throw new ArithmeticException("no count of places stands below " + this);
        }
        if (standsAbove(1)) {
            return 1;
        }
        int under = 1;
        int over = 2;
        while (!standsAbove(over)) {
            under = over;
            if (over > Integer.MAX_VALUE / 2) {
                throw new ArithmeticException(
                        "no decimal here names a number inside a distance this small");
            }
            over += over;
        }
        // The answer is above `under` and at or below `over`, and halving that keeps it so.
        while (over - under > 1) {
            int between = under + (over - under) / 2;
            if (standsAbove(between)) {
                over = between;
            } else {
                under = between;
            }
        }
        return over;
    }

    /** Whether this value stands above ten to the minus {@code places}, which is a comparison and
     *  builds neither side. */
    private boolean standsAbove(int places) {
        return compareTo(new ExactRatio(BigInteger.ONE, BigInteger.ONE, -places, -places)) > 0;
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
     *
     * @throws ArithmeticException where neither form is one this host writes, which is a number
     *         standing where no decimal and no pair of whole numbers reaches it
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
}
