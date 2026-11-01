package souther.compiler.numeric;

import souther.compiler.collect.HeldByKey;
import souther.compiler.collect.HeldByPair;
import souther.compiler.collect.HeldOnce;
import souther.exact.ExactArithmetic;
import souther.exact.ExactDecimals;
import souther.exact.ExactFailure;
import souther.exact.ExactParts;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.function.BiFunction;

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
 * them as one. A reader asks {@link #spelled}, which names the number without writing the powers
 * out; the fraction itself is for this package's own arithmetic, and costs what writing them costs.
 */
public final class ExactRatio implements Comparable<ExactRatio> {

    private static final BigInteger FIVE = BigInteger.valueOf(5);

    public static final ExactRatio ZERO = new ExactRatio(ExactParts.ZERO);
    public static final ExactRatio ONE = new ExactRatio(new ExactParts(1, 1, 0, 0));

    /**
     * The value, in the one canonical form the arithmetic makes, and held as the arithmetic hands
     * it over: each operation reads it as it stands and the answer it gets back is kept as it comes,
     * so no step copies four numbers into a second object on the way in or on the way out.
     */
    private final ExactParts parts;

    /** The value {@code numerator / denominator × 2^twos × 5^fives}, in whatever form it is
     *  written. */
    public ExactRatio(BigInteger numerator, BigInteger denominator, long twos, long fives) {
        this(ExactArithmetic.canonical(numerator, denominator, twos, fives));
    }

    /** A plain fraction, which is one with no power of two or five taken out of it yet. */
    public ExactRatio(BigInteger numerator, BigInteger denominator) {
        this(numerator, denominator, 0, 0);
    }

    /** @param canonical parts in the canonical form, which nothing here checks again */
    private ExactRatio(ExactParts canonical) {
        this.parts = canonical;
    }

    /** The canonical numerator once two and five are taken out of it. */
    public BigInteger numeratorWithoutUnits() {
        return parts.numerator();
    }

    /** The canonical denominator once two and five are taken out of it, which is positive. */
    public BigInteger denominatorWithoutUnits() {
        return parts.denominator();
    }

    public long twos() {
        return parts.twos();
    }

    public long fives() {
        return parts.fives();
    }

    /** One canonical form per value, so equal parts are the equal values. Asked of every number a
     *  form holds. */
    @Override
    public boolean equals(Object other) {
        return this == other || (other instanceof ExactRatio ratio && parts.equals(ratio.parts));
    }

    @Override
    public int hashCode() {
        return parts.hashCode();
    }

    public static ExactRatio of(long whole) {
        return from(new ExactParts(whole, 1, 0, 0));
    }

    public static ExactRatio of(BigInteger whole) {
        if (whole.bitLength() > LARGEST_KEPT_BITS) {
            return madeOf(whole);
        }
        return WHOLES.get(whole, ExactRatio::madeOf);
    }

    private static ExactRatio madeOf(BigInteger whole) {
        return shared(ExactArithmetic.canonical(whole, BigInteger.ONE, 0, 0));
    }

    public static ExactRatio of(BigInteger numerator, BigInteger denominator) {
        return shared(ExactArithmetic.canonical(numerator, denominator, 0, 0));
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
        if (at.precision() > LARGEST_KEPT_DIGITS) {
            return madeOf(at);
        }
        return DECIMALS.get(at, ExactRatio::madeOf);
    }

    private static ExactRatio madeOf(BigDecimal at) {
        return shared(ExactArithmetic.canonical(at));
    }

    /**
     * The numbers above which a decimal or a whole number is converted and not kept, and a ratio is
     * operated on and its answer not kept, so that the tables hold a bounded number of bytes and not
     * only a bounded number of entries: at most a few megabytes with every slot full of numbers this
     * long. The numbers a compile asks for are bounds and coefficients a person wrote and what is
     * worked out of them, and are far below them.
     */
    private static final int LARGEST_KEPT_DIGITS = 100;
    private static final int LARGEST_KEPT_BITS = 332;

    /**
     * The ratios of the decimals and of the whole numbers asked last. A compile asks for the same
     * few of each over and over, in every form that holds them, and each ask would otherwise build
     * the exact parts and put them in canonical form again. A decimal is a key by its scale and its
     * unscaled value, which is what the ratio is a function of: two decimals of one value written
     * with different scales are two keys and have the one ratio.
     */
    private static final HeldByKey<BigDecimal, ExactRatio> DECIMALS = new HeldByKey<>(11);
    private static final HeldByKey<BigInteger, ExactRatio> WHOLES = new HeldByKey<>(11);

    /**
     * Ten to {@code power}, which is two to it and five to it: held as the two exponents, and never
     * written out, so a power of any size a long counts is held as one of a size nothing builds.
     * What is worked out of it afterwards is held only as far as the arithmetic holds it.
     */
    public static ExactRatio tenTo(long power) {
        return new ExactRatio(new ExactParts(1, 1, power, power));
    }

    /** The value an answer of the arithmetic comes to, put in canonical form — which hands the
     *  answer back as it is where it is in that form already. */
    private static ExactRatio from(ExactParts parts) {
        return shared(ExactArithmetic.canonical(parts));
    }

    /**
     * The ratios made last. A compile holds a great many ratios and few values: the same
     * coefficients and bounds are worked out again in every form and closure that holds them.
     */
    private static final HeldOnce<ExactRatio> MADE = new HeldOnce<>(14);

    /** The ratio {@code canonical} is, the one made before where it is still held — found by the
     *  parts, so that an ask that finds it makes nothing. */
    private static ExactRatio shared(ExactParts canonical) {
        return MADE.held(canonical, ratio -> ratio.parts, ExactRatio::new);
    }

    /**
     * The answers of each operation of two ratios asked last, by the two operands in the order they
     * were asked. A compile asks the same few sums, products and quotients of the same coefficients
     * and bounds over and over, and each ask would otherwise work the answer out again and put it in
     * canonical form.
     *
     * <p>Every answer of operands of a size to keep comes from here, a sum with nought and a product
     * with one among them: what an operation answers without the arithmetic is still an answer made
     * at every ask, and is worked out once as the others are.
     *
     * <p>Kept only where the operands and the value are no wider than {@link #LARGEST_KEPT_BITS}
     * ({@link #keptBy}, {@link #kept}), so that the tables hold a bounded number of bytes and not only
     * a bounded number of entries — at most a few megabytes a table with every slot full of numbers
     * that wide. Two operands far apart in scale can have a sum of any number of digits, and that sum
     * is worked out at every ask. Of the answers that are no value, only the one that says there is
     * none is kept ({@link #kept}).
     */
    private static final HeldByPair<ExactRatio, ExactRatio, ExactAnswer<ExactRatio>> SUMS =
            new HeldByPair<>(11);
    private static final HeldByPair<ExactRatio, ExactRatio, ExactAnswer<ExactRatio>> PRODUCTS =
            new HeldByPair<>(11);
    private static final HeldByPair<ExactRatio, ExactRatio, ExactAnswer<ExactRatio>> QUOTIENTS =
            new HeldByPair<>(11);

    /** What {@code work} answers for this and {@code other}, kept in {@code answers} where the two
     *  are of a size to keep. */
    private ExactAnswer<ExactRatio> answered(
            HeldByPair<ExactRatio, ExactRatio, ExactAnswer<ExactRatio>> answers, ExactRatio other,
            BiFunction<ExactRatio, ExactRatio, ExactAnswer<ExactRatio>> work) {
        if (!keptBy(this) || !keptBy(other)) {
            return work.apply(this, other);
        }
        return answers.get(this, other, work, ExactRatio::kept);
    }

    /** Whether a ratio is of a size the tables keep: neither of its two numbers wider than a whole
     *  number {@link #WHOLES} keeps. Asked of every operand, and nearly every one is held in longs,
     *  which answers without counting bits. */
    private static boolean keptBy(ExactRatio ratio) {
        return ratio.parts.inLongs() || ratio.parts.widestBits() <= LARGEST_KEPT_BITS;
    }

    /**
     * Whether an answer is one the tables keep: one that is a function of the operands alone, and of
     * a size to keep. A value is, where it is no wider than the operands may be. That a value has no
     * representation is a fact about the number, so it is too. That the host had no room for it is a
     * fact about the run that asked, which another run with more room answers, so it is never kept.
     */
    static boolean kept(ExactAnswer<ExactRatio> answer) {
        return switch (answer) {
            case ExactAnswer.Held<ExactRatio> held -> keptBy(held.value());
            case ExactAnswer.Unheld<ExactRatio> unheld -> switch (unheld.why()) {
                case NO_REPRESENTATION_EXISTS -> true;
                case MORE_ROOM_COULD_ANSWER -> false;
            };
        };
    }

    /**
     * This as the one fraction it is, with the powers of two and five written into the two numbers.
     *
     * <p><b>The digits, and only for an algorithm that needs the digits</b> — a whole number handed
     * to something that counts in whole numbers. It costs what the exponents say, which is the cost
     * this type is held the way it is to avoid, so reaching for it is reaching past the
     * representation. Never for naming a number to a reader: {@link #spelled} does that, and does it
     * for every value this holds.
     *
     * <p>Visible to this package alone, so that a reader elsewhere cannot reach the digits at all.
     * And inside it only for a caller that has already asked whether the digits are few
     * ({@link #spelled}): it throws where the host holds no number that large, which no reasoning
     * step can be handed. A step that needs a whole number's digits asks {@link #wholeNumber},
     * which says so instead.
     *
     * <p>Everything a reasoning step asks of the two numbers is asked of this type instead:
     * {@link #numeratorMod} and {@link #denominatorMod} for a residue, {@link #numeratorAsRatio} for
     * the one above the line as a value to go on computing with,
     * {@link #timesWhatItStandsOver} for a product with the one below it,
     * {@link #spread} for the part of the denominator no finite decimal divides. Each of those
     * answers from the factors and builds nothing.
     */
    Fraction asFraction() {
        return new Fraction(
                ExactArithmetic.written(numeratorWithoutUnits(),
                        ExactArithmetic.aboveTheLine(twos()), ExactArithmetic.aboveTheLine(fives())),
                ExactArithmetic.written(denominatorWithoutUnits(),
                        ExactArithmetic.belowTheLine(twos()), ExactArithmetic.belowTheLine(fives())));
    }

    /** A ratio with its powers of two and five spelled out: two whole numbers in lowest terms, the
     *  second of them positive. */
    record Fraction(BigInteger numerator, BigInteger denominator) {}

    /**
     * The digits of this whole number, or which way the host could not hold them.
     *
     * <p>For a step that counts in whole numbers and is handed a modulus or a period that is one:
     * the residue of a value modulo it is a question of the value's bits, and the modulus has to be
     * a number to be asked. A number of billions of digits is one a host holds no place for, and
     * that is an answer this gives; the step widens what it says, as every other step does where an
     * exact number is unheld. It is not one that throws, which is what would stop the compile over a
     * modulus the model never wrote down.
     *
     * @throws IllegalArgumentException where this is not a whole number, which is a caller's mistake
     *         and not a value this can hold
     */
    ExactAnswer<BigInteger> wholeNumber() {
        if (!isWhole()) {
            throw new IllegalArgumentException("not a whole number: " + this);
        }
        return ExactAnswer.of(() -> ExactArithmetic.written(numeratorWithoutUnits(),
                ExactArithmetic.aboveTheLine(twos()), ExactArithmetic.aboveTheLine(fives())));
    }

    /** The number above this ratio's line, as a ratio — so that a caller going on to compute with it
     *  is handed the factors rather than the digits. */
    ExactRatio numeratorAsRatio() {
        return from(parts.numeratorOverOne(Math.max(twos(), 0), Math.max(fives(), 0)));
    }

    /**
     * This times what {@code other} stands over, or which way the arithmetic could not hold it.
     *
     * <p>Asked as the one product and not as a product with the denominator taken first. A
     * denominator at the least exponent has an exponent no long holds, while the product it goes into
     * can have one that does — so forming it would refuse an answer that was never out of range. The
     * exponents are added as whole numbers and only the last of them has to be a long.
     */
    ExactAnswer<ExactRatio> timesWhatItStandsOver(ExactRatio other) {
        if (isZero()) {
            return ExactAnswer.held(ZERO);
        }
        ExactParts scaled;
        try {
            scaled = ExactArithmetic.times(
                    parts, other.parts.denominatorOverOne(0, 0));
        } catch (ExactFailure failure) {
            return ExactAnswer.unheld(UnheldNumber.of(failure));
        }
        BigInteger scaledTwos = BigInteger.valueOf(scaled.twos()).add(belowTheLineBy(other.twos()));
        BigInteger scaledFives = BigInteger.valueOf(scaled.fives()).add(belowTheLineBy(other.fives()));
        if (!fitsALong(scaledTwos) || !fitsALong(scaledFives)) {
            return ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS);
        }
        return ExactAnswer.of(() -> from(
                scaled.withExponents(scaledTwos.longValue(), scaledFives.longValue())));
    }

    /** How many of a prime the denominator carries for this exponent, as a whole number because the
     *  least long has a negation no long holds. */
    private static BigInteger belowTheLineBy(long exponent) {
        return BigInteger.valueOf(exponent).negate().max(BigInteger.ZERO);
    }

    private static boolean fitsALong(BigInteger exponent) {
        return exponent.bitLength() < Long.SIZE;
    }

    /**
     * What dividing this by {@code other} comes to, as far as anything but its exponents goes: the
     * fraction it stands over and its two exponents as whole numbers.
     *
     * <p>Nothing here is built past what a quotient's own numbers are, and the exponents are not
     * bounded by a long, which is why a question about the quotient that does not need the exponents
     * to be held — whether it is whole, whether it is a decimal — can be answered where the quotient
     * itself has no representation.
     */
    private record QuotientShape(boolean overOne, BigInteger twos, BigInteger fives) {}

    private QuotientShape quotientShape(ExactRatio other) {
        return new QuotientShape(quotientOverOne(other),
                BigInteger.valueOf(twos()).subtract(BigInteger.valueOf(other.twos())),
                BigInteger.valueOf(fives()).subtract(BigInteger.valueOf(other.fives())));
    }

    /**
     * Whether the fraction this over {@code other} stands over is one: each fraction being in lowest
     * terms, that is this one's denominator dividing the other's and the other's numerator dividing
     * this one's — asked of the longs they are where a long holds every one of them.
     */
    private boolean quotientOverOne(ExactRatio other) {
        if (parts.inLongs() && other.parts.inLongs()
                && parts.numeratorInALong() != Long.MIN_VALUE
                && other.parts.numeratorInALong() != Long.MIN_VALUE) {
            return other.parts.denominatorInALong() % parts.denominatorInALong() == 0
                    && parts.numeratorInALong() % other.parts.numeratorInALong() == 0;
        }
        BigInteger acrossOne = ExactArithmetic.commonFactor(
                numeratorWithoutUnits(), other.numeratorWithoutUnits());
        BigInteger acrossTwo = ExactArithmetic.commonFactor(
                denominatorWithoutUnits(), other.denominatorWithoutUnits());
        return denominatorWithoutUnits().divide(acrossTwo)
                .multiply(other.numeratorWithoutUnits().abs().divide(acrossOne))
                .equals(BigInteger.ONE);
    }

    /**
     * Whether this is a whole multiple of {@code other}, which is a fact about the two values and
     * not about the quotient having a representation here.
     *
     * @throws ArithmeticException where {@code other} is zero
     */
    public boolean isWholeMultipleOf(ExactRatio other) {
        if (other.isZero()) {
            throw new ArithmeticException("divided by zero");
        }
        if (isZero()) {
            return true;
        }
        QuotientShape shape = quotientShape(other);
        return shape.overOne() && shape.twos().signum() >= 0 && shape.fives().signum() >= 0;
    }

    /**
     * Whether this is {@code other} times a decimal a model can write, by the same rule as
     * {@link #fitsWrittenDecimal}, and asked without the quotient being held.
     *
     * @throws ArithmeticException where {@code other} is zero
     */
    public boolean isWrittenDecimalMultipleOf(ExactRatio other) {
        if (other.isZero()) {
            throw new ArithmeticException("divided by zero");
        }
        if (isZero()) {
            return true;
        }
        QuotientShape shape = quotientShape(other);
        BigInteger leastScale = shape.twos().negate().max(shape.fives().negate());
        return shape.overOne() && leastScale.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) <= 0;
    }

    /**
     * This value as so much of a quantity coming to so much, which is how a rule writes a line:
     * {@code 3 * x <= 1} puts the line at a third.
     *
     * @param comesTo what that much of the quantity comes to
     * @param per     how much of the quantity, which is whole and above nought
     */
    public record Terms(ExactRatio comesTo, ExactRatio per) {}

    /**
     * This value in the one pair of terms that writes it.
     *
     * <p>Lowest terms, both whole, wherever lowest terms are numbers this type holds — which is
     * everywhere but the least exponent. A value at the least exponent stands over a power one past
     * any exponent there is, so what it is written per stops at the greatest one, and the one two or
     * five left over stays with what it comes to. Either way the pair follows from the value alone,
     * so two rules drawing one line write it one way, and a position built from the pair is one
     * position however the line was reached.
     *
     * <p>Total, and built from the exponents alone.
     */
    public Terms asTerms() {
        long perTwos = perOf(twos());
        long perFives = perOf(fives());
        return new Terms(
                from(parts.numeratorOverOne(twos() + perTwos, fives() + perFives)),
                from(parts.denominatorOverOne(perTwos, perFives)));
    }

    /** How much of one prime a value written per so much stands over: none for an exponent at or
     *  above nought, its negation below, and the greatest exponent where the negation is none. */
    private static long perOf(long exponent) {
        if (exponent >= 0) {
            return 0;
        }
        return exponent == Long.MIN_VALUE ? Long.MAX_VALUE : -exponent;
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
        return residue(numeratorWithoutUnits(),
                ExactArithmetic.aboveTheLine(twos()), ExactArithmetic.aboveTheLine(fives()), modulus);
    }

    /** What this ratio stands over, modulo {@code modulus}.
     *
     *  @param modulus a positive whole number */
    public BigInteger denominatorMod(BigInteger modulus) {
        return residue(denominatorWithoutUnits(),
                ExactArithmetic.belowTheLine(twos()), ExactArithmetic.belowTheLine(fives()), modulus);
    }

    private static BigInteger residue(
            BigInteger of, BigInteger twos, BigInteger fives, BigInteger modulus) {
        return of.mod(modulus)
                .multiply(BigInteger.TWO.modPow(twos, modulus))
                .multiply(FIVE.modPow(fives, modulus))
                .mod(modulus);
    }

    /**
     * The sum of {@code terms}, or which way the arithmetic could not hold it — the same answer for
     * the same terms in whatever order they are handed.
     *
     * <p>A sum of many is not a run of {@link #plus}: a run asks every partial sum to be held, and
     * a partial sum can fail where the whole does not — two terms far apart in scale where a third
     * cancels one of them, or two terms at the greatest exponent where the next two cancel both.
     * The arithmetic's own sum of many forms no partial sum in canonical form and meets the terms by
     * scale ({@link ExactArithmetic#sum}), so the answer is the terms' and not their order's, and a
     * sum is refused only where it has no representation or no room to be formed.
     */
    public static ExactAnswer<ExactRatio> sum(Collection<ExactRatio> terms) {
        List<ExactParts> parts = new ArrayList<>(terms.size());
        terms.forEach(each -> parts.add(each.parts));
        return ExactAnswer.of(() -> from(ExactArithmetic.sum(parts)));
    }

    /**
     * The sum, or which way the arithmetic could not hold it.
     *
     * <p>The one operation a model's own numbers reach a failure through: the exact sum of a decimal
     * near the end of the scale range and an ordinary one has as many digits as the two exponents are
     * apart, and a host has no room for that or no representation for it at all. See
     * {@link ExactAnswer}.
     */
    public ExactAnswer<ExactRatio> plus(ExactRatio other) {
        return answered(SUMS, other, ExactRatio::sumOf);
    }

    private static ExactAnswer<ExactRatio> sumOf(ExactRatio a, ExactRatio b) {
        // A sum with nought is the other term, which is canonical already; a good part of the sums
        // the constraint algebra asks are with a coefficient a form does not name.
        if (b.isZero()) {
            return ExactAnswer.held(a);
        }
        if (a.isZero()) {
            return ExactAnswer.held(b);
        }
        return ExactAnswer.of(() -> from(ExactArithmetic.plus(a.parts, b.parts)));
    }

    /** The difference, or which way the arithmetic could not hold it. Same failure as {@link #plus}:
     *  a difference is a sum of the negation, and is asked as one, so that the two share what is
     *  kept of them. */
    public ExactAnswer<ExactRatio> minus(ExactRatio other) {
        return plus(other.negated());
    }

    /** {@code of} negated, which a canonical form is again: the sign is the numerator's alone. */
    private static ExactParts negation(ExactParts of) {
        if (of.inLongs() && of.numeratorInALong() != Long.MIN_VALUE) {
            return new ExactParts(-of.numeratorInALong(), of.denominatorInALong(), of.twos(),
                    of.fives());
        }
        return new ExactParts(of.numerator().negate(), of.denominator(), of.twos(), of.fives());
    }

    /**
     * The product, or which way the arithmetic could not hold it.
     *
     * <p>The exponents add, and two exponents near the end of the range a long holds add to one
     * past it. That answer is a value this type has no place for, so it is said as an answer and not
     * thrown. See {@link ExactAnswer}.
     */
    public ExactAnswer<ExactRatio> times(ExactRatio other) {
        return answered(PRODUCTS, other, ExactRatio::productOf);
    }

    private static ExactAnswer<ExactRatio> productOf(ExactRatio a, ExactRatio b) {
        // A product with nought is nought whatever the other's exponents, and a product with one is
        // the other factor.
        if (a.isZero() || b.isZero()) {
            return ExactAnswer.held(ZERO);
        }
        if (b.equals(ONE)) {
            return ExactAnswer.held(a);
        }
        if (a.equals(ONE)) {
            return ExactAnswer.held(b);
        }
        return ExactAnswer.of(() -> from(ExactArithmetic.times(a.parts, b.parts)));
    }

    /**
     * This over {@code other}, or which way the arithmetic could not hold it. Asked directly and not
     * as a product with a reciprocal: the reciprocal of a value at the least exponent has no
     * exponent, while the quotient of that value by itself is one.
     *
     * @throws ArithmeticException where {@code other} is zero, which is a caller's mistake and not
     *          a value this can hold
     */
    public ExactAnswer<ExactRatio> dividedBy(ExactRatio other) {
        if (other.signum() == 0) {
            throw new ArithmeticException("divided by zero");
        }
        return answered(QUOTIENTS, other, ExactRatio::quotientOf);
    }

    private static ExactAnswer<ExactRatio> quotientOf(ExactRatio a, ExactRatio b) {
        if (a.isZero()) {
            return ExactAnswer.held(ZERO);
        }
        if (b.equals(ONE)) {
            return ExactAnswer.held(a);
        }
        return ExactAnswer.of(() -> from(ExactArithmetic.dividedBy(a.parts, b.parts)));
    }

    public ExactRatio negated() {
        if (isZero()) {
            return this;
        }
        if (!keptBy(this)) {
            return shared(negation(parts));
        }
        return NEGATIONS.get(this, ratio -> shared(negation(ratio.parts)));
    }

    /**
     * The negations of the ratios negated last, by the ratio: a negation is a function of the value
     * alone, and a compile negates the same few coefficients and bounds over and over.
     *
     * <p>A table and not a field on the ratio. A ratio holding its negation holds a ratio that holds
     * it, so every ratio negated would be a graph that holds itself, and every answer holding one a
     * value a walk of what answers hold cannot get to the end of.
     */
    private static final HeldByKey<ExactRatio, ExactRatio> NEGATIONS = new HeldByKey<>(11);

    public ExactRatio abs() {
        return signum() < 0 ? negated() : this;
    }

    public int signum() {
        return parts.signum();
    }

    public boolean isZero() {
        return parts.isZero();
    }

    /** Whether this is a whole number, which is a fraction of one with no power below the line. */
    public boolean isWhole() {
        return isZero() || (parts.overOne() && twos() >= 0 && fives() >= 0);
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
        return denominatorWithoutUnits();
    }

    /**
     * Where this stands against {@code other}, by exact value.
     *
     * <p>An order always exists, so this answers every pair — including the ones whose powers no
     * machine writes down. Two of those are a decimal written at either end of the scale a model may
     * write, so it is not an end of the range nothing reaches. Cross-multiplying would write out the
     * difference between their exponents, which is why the order is read from brackets of a working
     * width and not from the numbers ({@link ExactArithmetic#compare}).
     *
     * <p>An order only brackets settle is kept by the pair, as the answers of the operations are
     * ({@link #SUMS}), where both are of a size to keep: a compile orders the same few bounds against
     * each other over and over, and two bounds whose exponents are far apart are ordered by brackets
     * built afresh at every ask. An order the arithmetic settles without them is asked again, since it
     * costs less than a look into the table and makes nothing. An order that needed more room than
     * the host had is thrown and so not kept.
     */
    @Override
    public int compareTo(ExactRatio other) {
        int settled = ExactArithmetic.compareWithoutBrackets(parts, other.parts);
        if (settled != ExactArithmetic.UNSETTLED) {
            return settled;
        }
        if (!keptBy(this) || !keptBy(other)) {
            return ExactArithmetic.compare(parts, other.parts);
        }
        return ORDERS.get(this, other, ExactRatio::orderOf, order -> true);
    }

    private static final HeldByPair<ExactRatio, ExactRatio, Integer> ORDERS = new HeldByPair<>(11);

    private static Integer orderOf(ExactRatio a, ExactRatio b) {
        return ExactArithmetic.compare(a.parts, b.parts);
    }

    /** What {@link #times} answers where the product is more than a long holds. */
    private static final long TOO_LARGE = -1;

    /** How many bits the magnitude of {@code whole} takes, as {@link BigInteger#bitLength} counts
     *  them for any but the least long, which this counts as sixty-four. */
    private static int bitsOf(long whole) {
        return Long.SIZE - Long.numberOfLeadingZeros(Math.abs(whole));
    }

    /** {@code x · y} for two longs that are not negative, or {@link #TOO_LARGE}. */
    private static long times(long x, long y) {
        if (x == TOO_LARGE || y == TOO_LARGE) {
            return TOO_LARGE;
        }
        long low = x * y;
        return Math.multiplyHigh(x, y) != 0 || low < 0 ? TOO_LARGE : low;
    }

    /**
     * The largest whole number no greater than this, or which way the arithmetic could not hold it.
     *
     * <p>Read the way the order is read, and for the same reason. How large a value is and how large
     * the whole number below it is are two questions: two powers that all but cancel leave a value
     * of about one, whose floor is one digit and whose two numbers are hundreds of millions. A step
     * that worked the second out by writing the value down refused such a value over an answer that
     * was never going to be large. A value at the end of the scale range is the case where that
     * answer itself has no representation, which {@link ExactAnswer} says rather than throws.
     */
    public ExactAnswer<BigInteger> floor() {
        return rounded(RoundingMode.FLOOR, 0);
    }

    /** The smallest whole number no less than this, or which way the arithmetic could not hold it. */
    public ExactAnswer<BigInteger> ceiling() {
        return rounded(RoundingMode.CEILING, 0);
    }

    /** This with the part of it past the point dropped, which is towards nought from either side, or
     *  which way the arithmetic could not hold it. */
    public ExactAnswer<BigInteger> truncated() {
        return rounded(RoundingMode.DOWN, 0);
    }

    /**
     * The whole number {@code this × 10^scale} comes to, rounded the way {@code towards} says, or
     * which way the arithmetic could not hold it.
     *
     * <p>The tens stay a count and never become a ratio. Made into one they would have had to fit
     * the exponents a ratio holds, and a value whose powers all but cancel sits well inside those
     * while either of its own exponents stands at the end of them — so a step on the way would have
     * refused a value and an answer both of which are small.
     */
    private ExactAnswer<BigInteger> rounded(RoundingMode towards, int scale) {
        return ExactAnswer.of(() -> {
            try {
                return ExactArithmetic.roundedTimesTenTo(parts, scale, towards);
            } catch (IllegalArgumentException _) {
                throw new ArithmeticException(
                        "no whole number is this value, and none was to be chosen for it");
            }
        });
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
        long twos = Math.min(a.twos(), b.twos());
        long fives = Math.min(a.fives(), b.fives());
        if (a.parts.inLongs() && b.parts.inLongs()
                && bitsOf(a.parts.numeratorInALong()) < Long.SIZE - 1
                && bitsOf(b.parts.numeratorInALong()) < Long.SIZE - 1) {
            long tops = ExactArithmetic.commonFactor(
                    Math.abs(a.parts.numeratorInALong()), Math.abs(b.parts.numeratorInALong()));
            long below = a.parts.denominatorInALong();
            long belowToo = b.parts.denominatorInALong();
            long bottoms = times(below / ExactArithmetic.commonFactor(below, belowToo), belowToo);
            if (bottoms != TOO_LARGE) {
                return from(new ExactParts(tops, bottoms, twos, fives));
            }
        }
        BigInteger tops = ExactArithmetic.commonFactor(
                a.numeratorWithoutUnits().abs(), b.numeratorWithoutUnits().abs());
        BigInteger common = ExactArithmetic.commonFactor(
                a.denominatorWithoutUnits(), b.denominatorWithoutUnits());
        BigInteger bottoms = a.denominatorWithoutUnits().divide(common)
                .multiply(b.denominatorWithoutUnits());
        return shared(ExactArithmetic.canonical(tops, bottoms, twos, fives));
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
        return isZero() || parts.overOne();
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
        return Math.max(saturatingNegation(twos()), saturatingNegation(fives()));
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
        long twos = twos() + scale;
        long fives = fives() + scale;
        if (((twos() ^ twos) & (scale ^ twos)) >= 0 && ((fives() ^ fives) & (scale ^ fives)) >= 0) {
            return twos >= 0 && fives >= 0 && ExactArithmetic.canBeWritten(parts, twos, fives);
        }
        BigInteger byTwos = byTwosAt(scale);
        BigInteger byFives = byFivesAt(scale);
        if (byTwos.signum() < 0 || byFives.signum() < 0) {
            return false;
        }
        return ExactArithmetic.canBeWritten(numeratorWithoutUnits(), byTwos, byFives);
    }

    /** How many twos the unscaled value at {@code scale} carries, as a whole number, since the sum
     *  is one a long need not hold. */
    private BigInteger byTwosAt(long scale) {
        return BigInteger.valueOf(twos()).add(BigInteger.valueOf(scale));
    }

    private BigInteger byFivesAt(long scale) {
        return BigInteger.valueOf(fives()).add(BigInteger.valueOf(scale));
    }

    /**
     * This as a decimal a model could write, with the three ways it can come to none kept apart.
     *
     * <p>A ratio terminates exactly where its denominator is made of the factors ten is made of,
     * which here is where nothing is left below the line once both of them are held as exponents. A
     * third does not, and answering that with a rounded decimal is what this exists to stop: the
     * caller asking has to know whether it was handed the value or an approximation of it, and a
     * number that came back cannot be asked which it was.
     *
     * <p>A held empty answer says no decimal is this value: a third, or a value past the scale a
     * decimal has, which is the other way a value is not one and is settled by
     * {@link #fitsWrittenDecimal}. Both are facts about the number.
     *
     * <p>An unheld answer says the host had no room to write the decimal out: a value this says is
     * a decimal, written at a scale this language has, whose digits are more than a whole number
     * this host addresses. That is a fact about the run and says nothing about which values exist.
     * Handed back as an empty answer it would become the answer that no decimal is this value — and
     * then a coset would have said it holds nothing, a bound that no value stands at it, and a
     * search that a position has nowhere to go. What a machine ran out of is not what a set
     * contains.
     *
     * <p>The only way to ask a number for its digits: there is no member that throws for want of
     * room, so a reader that reads the difference off the type has no failure to catch and none can
     * turn it into an absence by accident.
     */
    public ExactAnswer<Optional<BigDecimal>> writtenDecimal() {
        return ExactAnswer.of(() -> Optional.ofNullable(written()));
    }

    private BigDecimal written() {
        if (isZero()) {
            return BigDecimal.ZERO;
        }
        if (!parts.overOne()) {
            return null;
        }
        if (!fitsWrittenDecimal()) {
            return null;
        }
        long scale = scaleOfTheDecimal();
        long digits = digitsInALong(scale);
        if (digits != 0) {
            return BigDecimal.valueOf(digits, (int) scale);
        }
        return new BigDecimal(
                ExactArithmetic.written(numeratorWithoutUnits(), byTwosAt(scale), byFivesAt(scale)),
                (int) scale);
    }

    /**
     * The numerator with two and five to its exponents moved by {@code scale} multiplied in, where a
     * long holds it and both are at or above nought; nought where not, which this value is not, so
     * nought says only that the digits are wider than a long.
     */
    private long digitsInALong(long scale) {
        if (!parts.inLongs() || parts.numeratorInALong() == Long.MIN_VALUE) {
            return 0;
        }
        long byTwos = twos() + scale;
        long byFives = fives() + scale;
        if (((twos() ^ byTwos) & (scale ^ byTwos)) < 0 || ((fives() ^ byFives) & (scale ^ byFives)) < 0
                || byTwos < 0 || byFives < 0) {
            return 0;
        }
        long magnitude = ExactArithmetic.raised(Math.abs(parts.numeratorInALong()), byTwos, byFives);
        return parts.numeratorInALong() < 0 ? -magnitude : magnitude;
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
        return from((signum() < 0 ? parts.negated() : parts).withExponents(0, 0));
    }

    /**
     * This as a decimal, rounded the way {@code towards} says where it is not one exactly, or which
     * way the arithmetic could not hold it.
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
    public ExactAnswer<BigDecimal> asDecimal(RoundingMode towards, int scale) {
        return switch (rounded(towards, scale)) {
            case ExactAnswer.Held<BigInteger> held -> ExactAnswer.held(new BigDecimal(held.value(), scale));
            case ExactAnswer.Unheld<BigInteger> unheld -> ExactAnswer.unheld(unheld.why());
        };
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
        return parts.numeratorSpelled() + "/" + parts.denominatorSpelled() + ";" + twos() + ";" + fives();
    }

    /**
     * The fewest places a decimal needs before the last of them lands inside this value: the least
     * count above nought with this value standing above ten to the minus that — or empty where no
     * count an {@code int} names does.
     *
     * <p>For a search that has to name a number inside a distance and wants to know how far in to
     * look. The count is what the value's size says, so it is read off the order rather than by
     * forming one over the value and counting its digits — a distance of a millionth has an answer
     * of about a million, and a number of that many digits built to be measured is the work this
     * type is held the way it is to avoid.
     *
     * <p>Binary search over the whole of what an {@code int} holds and not a bound doubled up to
     * it: a search that gives up once its own doubling passes half of {@link Integer#MAX_VALUE}
     * answers nothing for a count between there and the top of the range, though one may hold —
     * the range is one comparison to ask about outright and thirty-one more to place the answer
     * inside it, so nothing is bought by doubling up to it first.
     *
     * <p>{@link OptionalInt} and not {@link ExactAnswer}: this value is held exactly whatever its
     * scale, and no operation on it failed — what an {@code int} cannot name is the count, a metric
     * of the value and not the value itself, and {@link UnheldNumber} is the exact arithmetic's own
     * vocabulary for the second of those and answers nothing about the first. A caller folding this
     * into a wider {@code ExactAnswer} says which of its own words that is, since neither of
     * {@code UnheldNumber}'s is about a host language's {@code int}.
     *
     * @throws ArithmeticException where this value is at or below nought, which has no such count
     */
    public OptionalInt placesItStandsAbove() {
        if (signum() <= 0) {
            throw new ArithmeticException("no count of places stands below " + this);
        }
        if (standsAbove(1)) {
            return OptionalInt.of(1);
        }
        if (!standsAbove(Integer.MAX_VALUE)) {
            return OptionalInt.empty();
        }
        int under = 1;
        int over = Integer.MAX_VALUE;
        while (over - under > 1) {
            int between = under + (over - under) / 2;
            if (standsAbove(between)) {
                over = between;
            } else {
                under = between;
            }
        }
        return OptionalInt.of(over);
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
     * <p>Apart from {@link #key}, which names the value for telling two apart and is not read.
     *
     * <p>Past a thousand digits, in exponent notation rather than spelled out in full
     * ({@link ExactDecimals#spelledBounded}): a model's own decimals can be scaled far enough from
     * an ordinary one that the compact value behind them costs nothing to hold and everything to
     * write out, and a report is not the place that cost is asked to be paid. A decimal whose scale
     * is past what a {@code BigDecimal} has is written the way one would be, {@code 1E-4294967296},
     * so a number reads the same whichever of the two types carried it.
     *
     * <p>Where even that would spell the power out — a decimal with more twos than fives in it, or a
     * third a long way from nought — the power left over is named rather than written:
     * {@code 7 * 2^123 * 10^-4294967296}, {@code 1/3 * 10^-4294967296}. Ten is taken out first, so
     * at most one of two and five is left over.
     *
     * <p>Total, and one spelling per value: it is written from the canonical parts, so two equal
     * ratios spell alike and the length follows the digits of those parts and of the exponents,
     * never the exponents' size.
     */
    public String spelled() {
        if (isZero()) {
            return "0";
        }
        String inALong = spelledFromALong();
        if (inALong != null) {
            return inALong;
        }
        // Held wider than a long: the exponents' difference can be past what one holds.
        BigInteger tens = BigInteger.valueOf(Math.min(twos(), fives()));
        BigInteger twosLeft = BigInteger.valueOf(twos()).subtract(tens);
        BigInteger fivesLeft = BigInteger.valueOf(fives()).subtract(tens);
        if (!terminates()) {
            if (withinSpelling(numeratorWithoutUnits(),
                    ExactArithmetic.aboveTheLine(twos()), ExactArithmetic.aboveTheLine(fives()))
                    && withinSpelling(denominatorWithoutUnits(),
                    ExactArithmetic.belowTheLine(twos()), ExactArithmetic.belowTheLine(fives()))) {
                Fraction fraction = asFraction();
                return fraction.numerator() + "/" + fraction.denominator();
            }
            return inFactors(tens, twosLeft, fivesLeft);
        }
        if (twosLeft.signum() == 0 && fivesLeft.signum() == 0) {
            return inTens(numeratorWithoutUnits(), tens);
        }
        if (withinSpelling(numeratorWithoutUnits(), twosLeft, fivesLeft)) {
            return inTens(ExactArithmetic.written(numeratorWithoutUnits(), twosLeft, fivesLeft), tens);
        }
        return inFactors(tens, twosLeft, fivesLeft);
    }

    /**
     * {@link #spelled} of a finite decimal whose digits a long holds once ten is taken out of its two
     * exponents — a count, an amount, a decimal of a few places — written from that long; and null for
     * any other value, which is spelled from whole numbers of any width. A decimal of those digits at
     * that scale is the one the wider route makes, so the spelling is the same.
     */
    private String spelledFromALong() {
        if (!parts.inLongs() || parts.numeratorInALong() == Long.MIN_VALUE
                || parts.denominatorInALong() <= 0) {
            return null;
        }
        if (!parts.overOne()) {
            // The quotient of two whole numbers, each with the powers on its side of the line in it,
            // as asFraction writes it where both are short enough to spell.
            if (twos() <= Integer.MIN_VALUE || fives() <= Integer.MIN_VALUE) {
                return null;
            }
            long up = ExactArithmetic.raised(Math.abs(parts.numeratorInALong()),
                    Math.max(twos(), 0), Math.max(fives(), 0));
            long down = ExactArithmetic.raised(parts.denominatorInALong(),
                    Math.max(-twos(), 0), Math.max(-fives(), 0));
            if (up == 0 || down == 0) {
                return null;
            }
            return (parts.numeratorInALong() < 0 ? "-" : "") + up + "/" + down;
        }
        long tens = Math.min(twos(), fives());
        if (tens <= Integer.MIN_VALUE || tens > -(long) Integer.MIN_VALUE - 1
                || Math.max(twos(), fives()) > (long) Integer.MAX_VALUE) {
            return null;
        }
        long magnitude = ExactArithmetic.raised(Math.abs(parts.numeratorInALong()),
                twos() - tens, fives() - tens);
        if (magnitude == 0) {
            return null;
        }
        long digits = parts.numeratorInALong() < 0 ? -magnitude : magnitude;
        return ExactDecimals.spelledBounded(
                ExactDecimals.leastDigits(BigDecimal.valueOf(digits, (int) -tens)));
    }

    /**
     * Whether {@code whole × 2^twos × 5^fives} is short enough to spell out, asked of the parts and
     * without building it.
     *
     * <p>An upper bound on the digits: each part's share of the logarithm rounded up, and one more.
     * A number it lets through can land a little under the bound, never over it.
     */
    private static boolean withinSpelling(BigInteger whole, BigInteger twos, BigInteger fives) {
        BigInteger thousand = BigInteger.valueOf(1000);
        BigInteger digits = BigInteger.valueOf(whole.bitLength()).multiply(BigInteger.valueOf(302))
                .add(twos.multiply(BigInteger.valueOf(302)))
                .add(fives.multiply(BigInteger.valueOf(699)))
                .divide(thousand)
                .add(BigInteger.TWO);
        return digits.compareTo(BigInteger.valueOf(ExactDecimals.MAX_SPELT_OUT_DIGITS)) <= 0;
    }

    /**
     * {@code digits × 10^tens}, as a {@code BigDecimal} of that value writes itself.
     *
     * <p>Through the decimal where the scale is one a decimal has, so that the two agree by
     * construction. Past that the plain notation is longer than any bound, and the exponent notation
     * is written here the way {@link BigDecimal#toString} writes it: the digits with a point after
     * the first, and the power of ten that point stands for.
     */
    private static String inTens(BigInteger digits, BigInteger tens) {
        BigInteger scale = tens.negate();
        if (scale.bitLength() < Integer.SIZE) {
            return ExactDecimals.spelledBounded(
                    ExactDecimals.leastDigits(new BigDecimal(digits, scale.intValueExact())));
        }
        int precision = new BigDecimal(digits).precision();
        BigInteger point = tens.add(BigInteger.valueOf(precision - 1L));
        return new BigDecimal(digits, precision - 1) + "E" + (point.signum() < 0 ? "" : "+") + point;
    }

    /**
     * This value with the powers named rather than written: the fraction held, then what is left of
     * two or five once ten is taken out, then the tens.
     */
    private String inFactors(BigInteger tens, BigInteger twosLeft, BigInteger fivesLeft) {
        StringBuilder said = new StringBuilder(numeratorWithoutUnits().toString());
        if (!terminates()) {
            said.append('/').append(denominatorWithoutUnits());
        }
        if (twosLeft.signum() != 0) {
            said.append(" * 2^").append(twosLeft);
        }
        if (fivesLeft.signum() != 0) {
            said.append(" * 5^").append(fivesLeft);
        }
        if (tens.signum() != 0) {
            said.append(" * 10^").append(tens);
        }
        return said.toString();
    }

    /**
     * {@code d}, at its own scale, the same bounded way {@link #spelled} writes one — in exponent
     * notation past a thousand digits rather than spelled out in full.
     *
     * <p>For a caller holding a bare decimal rather than a ratio, so that this policy has one place
     * to be asked from and {@code souther.exact} stays a name only the numeric package reaches for:
     * a caller elsewhere in this compiler that wants a decimal written for a reader asks here rather
     * than importing the exact arithmetic's own package to do it a second way.
     */
    public static String spelledBounded(BigDecimal d) {
        return ExactDecimals.spelledBounded(d);
    }

    /**
     * The number as {@link #spelled} writes it.
     *
     * <p>Reached without being asked for — a record holding one of these prints it, and so does an
     * assertion that failed over one — so it is held to the same bound as a report and never writes
     * the powers out.
     */
    @Override
    public String toString() {
        return spelled();
    }
}
