package souther.runtime;

import org.jspecify.annotations.Nullable;
import souther.exact.ExactArithmetic;
import souther.exact.ExactFailure;
import souther.exact.ExactParts;
import souther.exact.ExactRangeExceeded;
import souther.exact.ExactRoomExceeded;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.function.LongConsumer;

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
 * <p>Held in one representation per value, so this record's own {@code equals} and {@code hashCode} are
 * the language's equality and hash, and {@link Values} reaches them through the arm that asks a value for
 * itself. The arithmetic on it — the canonical form, the four operations, the order and the rounding —
 * is {@link ExactArithmetic}'s, which the compiler's own exact ratios use as well; what this type adds is
 * being a value of the language and saying its failures in the language's terms.
 *
 * <p><b>Why the exponents are sixty-four bits.</b> Every {@code Int} and every {@code Decimal} has one
 * exact value here, and that is a rule rather than a range this type happens to cover (ADR-0116). What a
 * computation can ask for past this width aborts, as an {@code Int}'s overflow does (spec §jvm-abort).
 *
 * <p><b>Two failures, told apart.</b> An operation aborts where the answer has no representation, as a
 * {@link ConstraintViolation}. Where the run had no room for an instrument the answer needed, it fails as
 * {@link OutOfRoom}, and a platform that supplies what the decision wanted answers the same pair. Room is
 * what the platform supplies and not memory alone — how large a whole number its arithmetic builds is one
 * of the things a width can want more of. Being ordered is a fact about this type, so what a heap's size
 * may not decide is whether a {@code sort} over these is admitted and what it means, as against whether
 * one run of it finishes, which is what any operation is subject to.
 *
 * <p><b>The host's own limits leave by this type's abort.</b> A whole number is held by a host that has a
 * largest one, and a number past it is one no value here is made of — so no method of this type answers
 * with an exception of the host's arithmetic, which says nothing about a Rational to whoever reads it
 * (ADR-0112). The translation is here and not at the operators, because it is here that the host is
 * reached: {@code List.sum} over these asks this type for a sum directly, and an operator that caught what
 * it never called would have left the fold answering the other way.
 */
public record Rational(BigInteger numerator, BigInteger denominator, long twos, long fives)
        implements Comparable<Rational> {

    public static final Rational ZERO = new Rational(BigInteger.ZERO, BigInteger.ONE, 0, 0);
    public static final Rational ONE = new Rational(BigInteger.ONE, BigInteger.ONE, 0, 0);

    /**
     * How many bits of a value {@link #toString} will spell out. A rational's plain spelling is as
     * long as the number is, and a millionth of a millionth is not something a message is improved
     * by carrying — the same reason a {@code Decimal} at the ends of its scale range is described
     * rather than spelled (spec §jvm-abort). Beyond this the factored form is printed, which is
     * bounded by the size of what is stored.
     */
    private static final int SPELLED_BITS = 3322;

    public Rational {
        ExactParts canonical;
        try {
            canonical = ExactArithmetic.canonical(numerator, denominator, twos, fives);
        } catch (ExactFailure failure) {
            throw translated(failure);
        }
        numerator = canonical.numerator();
        denominator = canonical.denominator();
        twos = canonical.twos();
        fives = canonical.fives();
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

    private ExactParts parts() {
        return new ExactParts(numerator, denominator, twos, fives);
    }

    private static Rational from(ExactParts parts) {
        return new Rational(parts.numerator(), parts.denominator(), parts.twos(), parts.fives());
    }

    /** What a failure of the arithmetic is in this language's terms. */
    private static RuntimeException translated(ExactFailure failure) {
        return switch (failure) {
            case ExactRangeExceeded range -> new ConstraintViolation(range.reason());
            case ExactRoomExceeded room -> new OutOfRoom(room.reason());
        };
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
        try {
            return from(ExactArithmetic.reciprocal(parts()));
        } catch (ExactFailure failure) {
            throw translated(failure);
        }
    }

    public Rational times(Rational other) {
        try {
            return from(ExactArithmetic.times(parts(), other.parts()));
        } catch (ExactFailure failure) {
            throw translated(failure);
        }
    }

    public Rational dividedBy(Rational other) {
        try {
            return from(ExactArithmetic.dividedBy(parts(), other.parts()));
        } catch (ExactFailure failure) {
            throw translated(failure);
        }
    }

    public Rational plus(Rational other) {
        try {
            return from(ExactArithmetic.plus(parts(), other.parts()));
        } catch (ExactFailure failure) {
            throw translated(failure);
        }
    }

    public Rational minus(Rational other) {
        return plus(other.negated());
    }

    /** Where this stands against {@code other} by exact mathematical value, for every pair this type
     *  holds. */
    @Override
    public int compareTo(Rational other) {
        try {
            return ExactArithmetic.compare(parts(), other.parts());
        } catch (ExactFailure failure) {
            throw translated(failure);
        }
    }

    /**
     * This as a decimal where it has one exactly, and null where it has none. A caller that must
     * answer with a decimal whatever the value states its rounding at the point it asks.
     *
     * <p>The scale is where what the two exponents have in common goes, as far as a scale holds it — and
     * a scale is signed, so a value made of powers above nought is as compact a decimal as one made of
     * powers below it. What a scale does not reach stays among the digits, which is why the scale taken
     * is one that writes the value rather than the one that writes it most compactly: the compact one is
     * a choice, and past the end a scale counts it is a choice that refused values this type holds.
     */
    public @Nullable BigDecimal asDecimal() {
        if (!hasFiniteDecimal()) {
            return null;
        }
        // The scale first, which is the question about the answer; the digits after, which are the work.
        int scale = aScaleThatClearsBothExponents();
        try {
            return new BigDecimal(
                    ExactArithmetic.written(numerator,
                            BigInteger.valueOf(twos).add(BigInteger.valueOf(scale)),
                            BigInteger.valueOf(fives).add(BigInteger.valueOf(scale))),
                    scale);
        } catch (ExactFailure failure) {
            throw translated(failure);
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
            return ExactArithmetic.written(
                    numerator, BigInteger.valueOf(twos), BigInteger.valueOf(fives));
        } catch (ExactFailure failure) {
            throw translated(failure);
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    /**
     * This as a decimal of {@code scale} places, rounded by {@code towards}.
     *
     * <p>Where a caller must have a decimal whatever the value is. The scale goes to the exponents, not
     * the digits: the answer is the whole number this rounds to when multiplied by that power, beside the
     * scale it was asked at.
     */
    public BigDecimal asDecimal(int scale, java.math.RoundingMode towards) {
        try {
            return new BigDecimal(ExactArithmetic.roundedTimesTenTo(parts(), scale, towards), scale);
        } catch (ExactFailure failure) {
            throw translated(failure);
        } catch (IllegalArgumentException e) {
            throw new IllegalArgumentException(e.getMessage() + ": " + this, e);
        }
    }

    // What an evaluated computation asks: each operation above, paid for to a checkpoint (HostWork).
    // A value is paid for by the bits of the fraction it stores and not by its exponents, which it
    // holds as numbers; what an operation builds out of the exponents is paid for where it builds it.
    // Every operation answers in lowest terms with the twos and fives taken off, which divides the
    // answer by what it shares, so each pays for that too.

    /** {@link #times}, paid for to {@code checkpoint} first. */
    public Rational times(Rational other, WorkCheckpoint checkpoint) {
        payProduct(other, checkpoint);
        return times(other);
    }

    /** {@link #dividedBy}, paid for to {@code checkpoint} first. */
    public Rational dividedBy(Rational other, WorkCheckpoint checkpoint) {
        payProduct(other, checkpoint);
        return dividedBy(other);
    }

    /**
     * {@link #plus}, paid for to {@code checkpoint} first: each side's numerator is multiplied by the
     * powers of two and five it holds beyond what the two share, and the two are brought over one
     * denominator. Where a power is past what the host builds nothing is paid, since the sum then has
     * no representation and says so.
     */
    public Rational plus(Rational other, WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE && !isZero() && !other.isZero()) {
            long here = powerBits(twos, Math.min(twos, other.twos), fives, Math.min(fives, other.fives));
            long there = powerBits(other.twos, Math.min(twos, other.twos),
                    other.fives, Math.min(fives, other.fives));
            long over = HostWork.bits(denominator) + HostWork.bits(other.denominator);
            long sum = Math.max(HostWork.bits(numerator) + here, HostWork.bits(other.numerator) + there) + over;
            HostWork.pay(checkpoint, Math.max(here, there) + sum,
                    HostWork.power(here) + HostWork.power(there)
                            + HostWork.product(HostWork.bits(numerator), here)
                            + HostWork.product(HostWork.bits(other.numerator), there)
                            + HostWork.product(sum, over) + HostWork.product(sum, sum));
        }
        return plus(other);
    }

    /** {@link #minus}, paid for to {@code checkpoint} first. */
    public Rational minus(Rational other, WorkCheckpoint checkpoint) {
        return plus(other.negated(checkpoint), checkpoint);
    }

    /** {@link #negated}, paid for to {@code checkpoint} first. */
    public Rational negated(WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE) {
            checkpoint.spend(HostWork.product(stored(), stored()));
        }
        return negated();
    }

    /** {@link #of(BigInteger, BigInteger)}, paid for to {@code checkpoint} first: the two are taken to
     *  lowest terms, which divides each by what they share and by two and five as often as they hold
     *  them. */
    public static Rational of(BigInteger numerator, BigInteger denominator, WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE) {
            long bits = HostWork.bits(numerator) + HostWork.bits(denominator);
            checkpoint.spend(HostWork.product(bits, bits));
        }
        return of(numerator, denominator);
    }

    /** {@link #of(BigDecimal)}, paid for to {@code checkpoint} first: the digits are taken to lowest
     *  terms, which divides by two and five as often as they hold them. */
    public static Rational of(BigDecimal written, WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE) {
            checkpoint.spend(HostWork.product(HostWork.bits(written), HostWork.bits(written)));
        }
        return of(written);
    }

    /**
     * {@link #compareTo}, paid for to {@code checkpoint}: the writing the order may form before it
     * refines is paid for first, and each bracket the refinement takes is paid for as it is taken —
     * how many it takes turns on how closely the two agree, which nothing before asking says.
     */
    public int compareTo(Rational other, WorkCheckpoint checkpoint) {
        if (checkpoint == WorkCheckpoint.NONE) {
            return compareTo(other);
        }
        long stored = stored() + other.stored();
        long writing = 4 * stored + 128;
        checkpoint.spend(HostWork.power(writing) + HostWork.product(stored, writing));
        try {
            return ExactArithmetic.compare(parts(), other.parts(), widths(checkpoint, stored));
        } catch (ExactFailure failure) {
            throw translated(failure);
        }
    }

    /** {@link #asDecimal(int, java.math.RoundingMode)}, paid for to {@code checkpoint}: the digits of
     *  the answer are built from the exponents moved by the scale, and a value standing close to half
     *  of the way between two of them is refined as the order is. */
    public BigDecimal asDecimal(int scale, java.math.RoundingMode towards, WorkCheckpoint checkpoint) {
        if (checkpoint == WorkCheckpoint.NONE) {
            return asDecimal(scale, towards);
        }
        payWritten(twos + (long) scale, fives + (long) scale, checkpoint);
        try {
            return new BigDecimal(ExactArithmetic.roundedTimesTenTo(parts(), scale, towards,
                    widths(checkpoint, stored())), scale);
        } catch (ExactFailure failure) {
            throw translated(failure);
        } catch (IllegalArgumentException e) {
            throw new IllegalArgumentException(e.getMessage() + ": " + this, e);
        }
    }

    /** {@link #asDecimal()}, paid for to {@code checkpoint} first, where there is a decimal. */
    public @Nullable BigDecimal asDecimal(WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE && hasFiniteDecimal()) {
            long tens = Math.min(twos, fives);
            if (tens >= -(long) Integer.MAX_VALUE) {
                long scale = tens > -(long) Integer.MIN_VALUE ? Integer.MIN_VALUE : -tens;
                payWritten(twos + scale, fives + scale, checkpoint);
            }
        }
        return asDecimal();
    }

    /** {@link #asWholeNumber()}, paid for to {@code checkpoint} first, where it is one. */
    public @Nullable BigInteger asWholeNumber(WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE && isWhole()) {
            payWritten(twos, fives, checkpoint);
        }
        return asWholeNumber();
    }

    /** The bits of the fraction this stores. */
    long stored() {
        return HostWork.bits(numerator) + HostWork.bits(denominator);
    }

    /** Pays for multiplying two values' fractions together and taking the product to lowest terms. */
    private void payProduct(Rational other, WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE) {
            long a = stored();
            long b = other.stored();
            checkpoint.spend(HostWork.product(a, b) + HostWork.product(a + b, a + b));
        }
    }

    /** Pays for this numerator written out with {@code 2^twos} and {@code 5^fives} built into it, the
     *  part of each exponent below nought being left where it is. */
    private void payWritten(long byTwos, long byFives, WorkCheckpoint checkpoint) {
        long built = powerBits(Math.max(byTwos, 0), 0, Math.max(byFives, 0), 0);
        long answer = HostWork.bits(numerator) + built;
        HostWork.pay(checkpoint, answer, HostWork.power(built) + HostWork.product(stored(), answer)
                + HostWork.product(answer, HostWork.bits(denominator)));
    }

    /** The bits of {@code 2^(twos - fromTwos) × 5^(fives - fromFives)}, or past what the host builds
     *  where either difference is past what a long counts. */
    private static long powerBits(long twos, long fromTwos, long fives, long fromFives) {
        long byTwos = twos - fromTwos;
        long byFives = fives - fromFives;
        if (byTwos < 0 || byFives < 0 || byTwos > HostWork.MOST_BITS || byFives > HostWork.MOST_BITS) {
            return HostWork.MOST_BITS + 1;
        }
        return byTwos + byFives * 2322 / 1000 + 1;
    }

    /** What each bracket a refinement takes is paid: a power of five squared to that width a time for
     *  each bit of its exponent, and the stored fraction divided at it. */
    private static LongConsumer widths(WorkCheckpoint checkpoint, long stored) {
        return width -> checkpoint.spend(Long.SIZE * HostWork.product(width, width)
                + HostWork.product(stored, width));
    }

    /** The abort a whole number the host had no range for leaves by. */
    private static ConstraintViolation noRoomForIt(ArithmeticException thrown) {
        return new ConstraintViolation("no Rational holds a whole number that size: " + thrown.getMessage());
    }

    /** The numerator with the powers that multiply it built in. */
    private BigInteger numeratorWithItsPowers() {
        return ExactArithmetic.written(numerator,
                ExactArithmetic.aboveTheLine(twos), ExactArithmetic.aboveTheLine(fives));
    }

    /** The denominator with the powers that divide it built in. */
    private BigInteger denominatorWithItsPowers() {
        return ExactArithmetic.written(denominator,
                ExactArithmetic.belowTheLine(twos), ExactArithmetic.belowTheLine(fives));
    }

    /**
     * The value, spelled as one fraction where it is small enough to read and as the factored form
     * where it is not.
     *
     * <p>Bounded whichever way it goes, the parts as much as the powers. A part is as large as this
     * representation lets one be, which is millions of digits, and a spelling of one is a cost paid where
     * it may be least affordable: what carries these is an abort, and the abort the room ran out on is one
     * whose message would want more of it. So a part past what anyone reads is described by its size, as
     * the value itself is.
     */
    @Override
    public String toString() {
        // The exponents first, and by their own ends rather than through a magnitude: the least
        // sixty-four-bit number has no positive counterpart, so a reading that took one would answer
        // about a value it had already left.
        if (twos > SPELLED_BITS || twos < -SPELLED_BITS
                || fives > SPELLED_BITS || fives < -SPELLED_BITS
                || (long) numerator.abs().bitLength() + denominator.bitLength() > SPELLED_BITS) {
            return spelled(numerator) + "/" + spelled(denominator) + "×2^" + twos + "×5^" + fives;
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

    /** A stored part as it is written into a message: its digits where those are worth reading, and its
     *  size where they are not. */
    private static String spelled(BigInteger part) {
        return part.bitLength() > SPELLED_BITS
                ? "(a whole number of " + part.bitLength() + " bits)"
                : part.toString();
    }
}
