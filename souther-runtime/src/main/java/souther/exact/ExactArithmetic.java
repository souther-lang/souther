package souther.exact;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.Map;
import java.util.NavigableMap;
import java.util.NavigableSet;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.LongConsumer;

/**
 * Exact rational arithmetic on values held as {@code n/d · 2^a · 5^b}, which both the compiler's
 * {@code ExactRatio} and the run time's {@code Rational} are.
 *
 * <p><b>Why the powers of two and five stand apart.</b> A decimal is an unscaled whole number over a
 * power of ten, and a scale of a million is four bytes. Held as a plain numerator over a denominator,
 * embedding that decimal means building {@code 10^1000000} — a compact value becoming work proportional
 * to its scale by nothing more than entering exact arithmetic. So the factors ten is made of are kept as
 * exponents, and a decimal is taken in by two integer subtractions.
 *
 * <p>Ten is not enough on its own: a single power of ten cannot hold a half, whose only factor is a two,
 * and the two exponents of a value like a sixth are not equal. Two and five are therefore separate, and
 * what is left over — a third's three — stays in the numerator and the denominator.
 *
 * <p><b>One representation per value.</b> Every non-zero rational is uniquely {@code n/d · 2^a · 5^b}
 * where {@code n} and {@code d} are coprime and neither is divisible by two or by five: {@code a} is the
 * value's two-adic valuation, {@code b} its five-adic one, and what remains is a fraction in lowest
 * terms. So equal parts are equal values, and a type holding these can let its own {@code equals} and
 * {@code hashCode} be the value's.
 *
 * <p><b>Why the exponents are sixty-four bits, and all of them.</b> Every {@code Int} and every
 * {@code Decimal} has one exact value, and that is a rule rather than a range this arithmetic happens to
 * cover. A decimal's scale is thirty-two bits and enters as its negation, and negating the least
 * thirty-two-bit number leaves it — so an exponent held to a scale's own width would refuse a decimal the
 * widening is supposed to take.
 *
 * <p>Every long is an exponent a value may hold, the least one included. That a value is held and that
 * an operation on it has an answer are different questions: a quotient's exponents are the difference of
 * two held ones and a reciprocal's are a negation, and the least long has no positive counterpart. So the
 * operation that needs a negation is the one that refuses, and {@code r / r} is not refused for it.
 *
 * <p><b>What a step is allowed to refuse.</b> An operation fails where the answer has no representation,
 * and not where a step on the way to it has none. The shapes that separate the two are at the ends of
 * the exponent's range, which a run of squarings reaches and an ordinary model does not, so an operation
 * here is written so that what it builds is the answer's own parts.
 *
 * <p><b>What the exponents cost.</b> Multiplying and dividing add and subtract them and never build them.
 * Adding does build the difference between two exponents, because that is what the exact sum is:
 * {@code 1 + 1E-1000000} has a million digits whatever holds it. Comparing builds nothing for the pairs a
 * bracket separates, which is nearly all of them ({@link ExactOrder}).
 *
 * <p><b>What this does not bound.</b> Not the parts of a value, past what the host holds one of. Every
 * heterogeneous exact operation reads its other operand in here, and a {@code Decimal}'s unscaled value
 * is a whole number of whatever size the platform holds, so a bound on the parts would have refused a
 * {@code Decimal} that every rule says has an exact value here, and refused a comparison whose answer is a
 * {@code Bool}.
 *
 * <p>How a failure is spoken of is the caller's. {@link ExactRangeExceeded} and
 * {@link ExactRoomExceeded} say which of the two it was, and each caller puts it in the terms its own
 * layer uses.
 */
public final class ExactArithmetic {

    private ExactArithmetic() {
    }

    /**
     * The one canonical form of the value {@code numerator × 2^twos × 5^fives / denominator}.
     *
     * @throws IllegalArgumentException where a part is missing or the denominator is nought
     * @throws ExactRangeExceeded where the exponents the value comes to are past sixty-four bits
     */
    public static ExactParts canonical(
            BigInteger numerator, BigInteger denominator, long twos, long fives) {
        if (numerator == null || denominator == null) {
            throw new IllegalArgumentException("an exact rational is two whole numbers and two exponents");
        }
        if (denominator.signum() == 0) {
            throw new IllegalArgumentException("an exact rational has no zero denominator");
        }
        if (numerator.signum() == 0) {
            return ExactParts.ZERO;
        }
        if (denominator.signum() < 0) {
            numerator = numerator.negate();
            denominator = denominator.negate();
        }
        if (numerator.bitLength() < Long.SIZE && denominator.bitLength() < Long.SIZE
                && numerator.longValue() != Long.MIN_VALUE) {
            return canonical(numerator.longValue(), denominator.longValue(), twos, fives, null);
        }
        BigInteger common = commonFactor(numerator, denominator);
        if (!common.equals(BigInteger.ONE)) {
            numerator = numerator.divide(common);
            denominator = denominator.divide(common);
        }
        // The two sides are coprime by now, so a factor of two or of five is on one of them alone, and
        // taking it off one cannot put it back on the other.
        //
        // A power of two is where a number's bits stop, so it comes off in one reading of them and not a
        // division for each: this runs over every value made, and a loop dividing for each factor would
        // turn holding a whole number into work proportional to it.
        int inNumerator = numerator.getLowestSetBit();
        if (inNumerator > 0) {
            numerator = numerator.shiftRight(inNumerator);
            twos = ExactPowers.added(twos, inNumerator);
        }
        int inDenominator = denominator.getLowestSetBit();
        if (inDenominator > 0) {
            denominator = denominator.shiftRight(inDenominator);
            twos = ExactPowers.added(twos, -inDenominator);
        }
        // A five leaves no such mark, so the fives come off by division.
        long[] taken = new long[1];
        numerator = withoutFives(numerator, taken);
        fives = ExactPowers.added(fives, taken[0]);
        taken[0] = 0;
        denominator = withoutFives(denominator, taken);
        fives = ExactPowers.added(fives, -taken[0]);
        return new ExactParts(numerator, denominator, twos, fives);
    }

    /**
     * The one canonical form of the value a written decimal is: its unscaled value times two and five
     * to the negated scale, so the scale moves into the exponents and nothing is built.
     *
     * <p>A decimal whose unscaled value a long holds is read as one rather than through
     * {@link BigDecimal#unscaledValue}, which makes a {@code BigInteger} of it every time it is asked.
     * Whether a long holds it is asked by comparing with the least and the greatest long at a scale of
     * nought, which reads the sizes of the two and counts no digits: a digit count of a large value is
     * work that grows faster than the value does.
     */
    public static ExactParts canonical(BigDecimal written) {
        long exponent = -(long) written.scale();
        // Moved by its own scale, which leaves a scale of nought, so nothing is refused and the
        // unscaled value is the whole number this is.
        BigDecimal unscaled = written.scaleByPowerOfTen(written.scale());
        if (unscaled.compareTo(LEAST_LONG) >= 0 && unscaled.compareTo(GREATEST_LONG) <= 0) {
            return canonical(new ExactParts(unscaled.longValue(), 1, exponent, exponent));
        }
        return canonical(written.unscaledValue(), BigInteger.ONE, exponent, exponent);
    }

    private static final BigDecimal LEAST_LONG = BigDecimal.valueOf(Long.MIN_VALUE);

    private static final BigDecimal GREATEST_LONG = BigDecimal.valueOf(Long.MAX_VALUE);

    /**
     * The one canonical form of the value {@code parts} are, which is {@code parts} itself where they
     * are in it already — as the product and the quotient of two canonical values are, and as a
     * value handed back unchanged is — so that asking costs no new parts.
     *
     * @throws ExactRangeExceeded where the exponents the value comes to are past sixty-four bits
     */
    public static ExactParts canonical(ExactParts parts) {
        if (parts.isZero()) {
            return ExactParts.ZERO;
        }
        if (parts.inLongs() && parts.numeratorInALong() != Long.MIN_VALUE
                && parts.denominatorInALong() != Long.MIN_VALUE) {
            long numerator = parts.numeratorInALong();
            long denominator = parts.denominatorInALong();
            // Neither is the least long, so the negation of either is held.
            return denominator < 0
                    ? canonical(-numerator, -denominator, parts.twos(), parts.fives(), null)
                    : canonical(numerator, denominator, parts.twos(), parts.fives(), parts);
        }
        return canonical(parts.numerator(), parts.denominator(), parts.twos(), parts.fives());
    }

    /**
     * {@code of}, which is not nought, with every factor of five taken off, and how many were added
     * to {@code taken}.
     *
     * <p>Five to each power of two is tried while it divides what is left, and then each of those
     * powers once more from the largest down: a number holding {@code k} fives is divided about
     * {@code 2·log k} times, each by a power no larger than what comes off. One five at a time, a
     * whole number written out from a power of ten — a decimal rounded to a scale far from nought
     * is one — would be divided once per digit, each time across all of its digits.
     */
    private static BigInteger withoutFives(BigInteger of, long[] taken) {
        int levels = 0;
        BigInteger power = ExactPowers.FIVE;
        while (true) {
            BigInteger[] divided = of.divideAndRemainder(power);
            if (divided[1].signum() != 0) {
                break;
            }
            of = divided[0];
            taken[0] += 1L << levels;
            levels++;
            // A square with more bits than what is left cannot divide it.
            if (2L * power.bitLength() - 1 > of.bitLength()) {
                break;
            }
            power = power.multiply(power);
        }
        // Each power is squared up again rather than kept: the largest dominates the cost of all.
        for (int i = levels - 1; i >= 0; i--) {
            BigInteger[] divided = of.divideAndRemainder(fiveToTheTwoTo(i));
            if (divided[1].signum() == 0) {
                of = divided[0];
                taken[0] += 1L << i;
            }
        }
        return of;
    }

    /** Five to the power of two to the {@code level}. */
    private static BigInteger fiveToTheTwoTo(int level) {
        BigInteger power = ExactPowers.FIVE;
        for (int i = 0; i < level; i++) {
            power = power.multiply(power);
        }
        return power;
    }

    /**
     * The same canonical form, of a numerator other than the least long and a positive denominator,
     * worked out in longs.
     *
     * <p>Nearly every value the constraint algebra and a model's rationals make is this small, and
     * the steps are the ones above: the common factor off, then the twos where the bits stop, then
     * the fives one division each. In longs none of them allocates, where each division of a
     * {@code BigInteger} answers a new one, and a remainder check answers two. The least long is left
     * to the wide route because its magnitude is the one a long does not hold, and the numbers that
     * bound an {@code Int} are the ones beside it, which this takes.
     *
     * @param handed the parts these four numbers came from, handed back where they are canonical
     *               already, or null
     */
    private static ExactParts canonical(long numerator, long denominator, long twos, long fives,
                                        ExactParts handed) {
        // A division for each side is skipped where there is nothing to take off: most values are
        // whole numbers, and a denominator of one has no factor of two or five to look for.
        long common = denominator == 1 ? 1 : commonFactor(Math.abs(numerator), denominator);
        if (common != 1) {
            numerator /= common;
            denominator /= common;
        }
        int inNumerator = Long.numberOfTrailingZeros(numerator);
        if (inNumerator > 0) {
            numerator >>= inNumerator;
            twos = ExactPowers.added(twos, inNumerator);
        }
        while (numerator % 5 == 0) {
            numerator /= 5;
            fives = ExactPowers.added(fives, 1);
        }
        if (denominator != 1) {
            int inDenominator = Long.numberOfTrailingZeros(denominator);
            if (inDenominator > 0) {
                denominator >>= inDenominator;
                twos = ExactPowers.added(twos, -inDenominator);
            }
            while (denominator % 5 == 0) {
                denominator /= 5;
                fives = ExactPowers.added(fives, -1);
            }
        }
        if (handed != null && handed.numeratorInALong() == numerator
                && handed.denominatorInALong() == denominator
                && handed.twos() == twos && handed.fives() == fives) {
            return handed;
        }
        return new ExactParts(numerator, denominator, twos, fives);
    }

    /**
     * The greatest common factor of two whole numbers of any size, which is one wherever either is.
     *
     * <p>The one place a gcd of these is taken. A whole number is a fraction over one and the ends of
     * an integer type, the least and greatest long, are past the long route, so these come through
     * here at every read of such a bound; and a gcd with one is not free — it walks the bits of the
     * other.
     */
    public static BigInteger commonFactor(BigInteger a, BigInteger b) {
        return a.equals(BigInteger.ONE) || b.equals(BigInteger.ONE) ? BigInteger.ONE : a.gcd(b);
    }

    /** The greatest common factor of two positive longs. */
    public static long commonFactor(long a, long b) {
        while (b != 0) {
            long rest = a % b;
            a = b;
            b = rest;
        }
        return a;
    }

    /**
     * The powers of five a long holds with a bit to spare, by their exponent: past the last of them
     * a number raised by one is past what the long route holds whatever it was.
     */
    private static final long[] FIVES = fives();

    private static long[] fives() {
        long[] out = new long[27];
        out[0] = 1;
        for (int at = 1; at < out.length; at++) {
            out[at] = out[at - 1] * 5;
        }
        return out;
    }

    /** Whether both whole numbers of {@code parts} take the long route of a sum, a product or a
     *  quotient: a long holds each with a bit to spare, which the working of those is formed in. */
    private static boolean inLongs(ExactParts parts) {
        return parts.inLongs() && bits(parts.numeratorInALong()) < Long.SIZE - 1
                && bits(parts.denominatorInALong()) < Long.SIZE - 1;
    }

    /** How many bits the magnitude of {@code whole} takes, which the long route holds below
     *  sixty-three. */
    private static int bits(long whole) {
        return Long.SIZE - Long.numberOfLeadingZeros(Math.abs(whole));
    }

    /** Whether the product of two numbers the long route holds is one it holds as well. Asked of
     *  their lengths, so it turns away some products that would have fitted, and those go wide. */
    private static boolean multipliesInALong(long a, long b) {
        return bits(a) + bits(b) < Long.SIZE - 1;
    }

    /** Whether two exponents add up to one a long holds — the question {@link ExactPowers#added}
     *  answers by refusing, asked so that the refusal is left to the arithmetic at any width. */
    private static boolean addedInALong(long a, long b) {
        long sum = a + b;
        return ((a ^ sum) & (b ^ sum)) >= 0;
    }

    /** Whether the difference of two exponents is one a long holds, as {@link #addedInALong} asks of
     *  their sum. */
    private static boolean lessenedInALong(long a, long b) {
        long difference = a - b;
        return ((a ^ b) & (a ^ difference)) >= 0;
    }

    /**
     * {@code whole × 2^twos × 5^fives}, or nought where the long route does not hold it.
     *
     * <p>The exponents are each the distance from an exponent down to the lesser of two, so they are
     * never below nought, and a distance past what a long holds has wrapped: read unsigned, it is
     * the distance still, and far past any that is built here. {@code whole} is not nought, so
     * nought says nothing but that this went wide.
     */
    public static long raised(long whole, long twos, long fives) {
        if (Long.compareUnsigned(twos, Long.SIZE - 2) > 0
                || Long.compareUnsigned(fives, FIVES.length - 1) > 0) {
            return 0;
        }
        long five = FIVES[(int) fives];
        if (bits(whole) + (int) twos + bits(five) >= Long.SIZE - 1) {
            return 0;
        }
        return (whole << twos) * five;
    }

    /**
     * The product of {@code factors}: one answer for the factors in whatever order they come, refused
     * only where the product itself has no representation.
     *
     * <p>Not a run of {@link #times}, each of which asks its exponents to be held: two factors at the
     * greatest exponent fail where they meet even where a third brings the product back. A canonical
     * numerator and denominator hold no two and no five, so neither does their product, and the
     * product's exponents are the factors' added up — so they are added up, and asked of once. And a
     * product with a nought among its factors is nought, whatever the others' exponents add to.
     *
     * <p>The factors are walked and never gathered, twice: once for their exponents and whether one
     * is nought, and once to multiply them out.
     *
     * @throws ExactRangeExceeded where the exponents the factors add up to are past sixty-four bits
     */
    public static ExactParts product(Iterable<ExactParts> factors) {
        // Added up wider than a long, so that a sum that passes the end and comes back is the sum.
        BigInteger allTwos = BigInteger.ZERO;
        BigInteger allFives = BigInteger.ZERO;
        for (ExactParts each : factors) {
            if (each.isZero()) {
                return ExactParts.ZERO;
            }
            allTwos = allTwos.add(BigInteger.valueOf(each.twos()));
            allFives = allFives.add(BigInteger.valueOf(each.fives()));
        }
        if (allTwos.bitLength() >= Long.SIZE || allFives.bitLength() >= Long.SIZE) {
            throw new ExactRangeExceeded("the exponents of a product are past sixty-four bits: "
                    + allTwos + ", " + allFives);
        }
        long twos = allTwos.longValueExact();
        long fives = allFives.longValueExact();
        BigInteger numerator = BigInteger.ONE;
        BigInteger denominator = BigInteger.ONE;
        try {
            for (ExactParts each : factors) {
                numerator = numerator.multiply(each.numerator());
                denominator = denominator.multiply(each.denominator());
            }
        } catch (ArithmeticException e) {
            throw ExactPowers.hostLimit(e);
        }
        return canonical(numerator, denominator, twos, fives);
    }

    /**
     * The product. The exponents add and are never built, and the common factors of the two fractions are
     * taken off before the numerators and denominators are multiplied, so what is multiplied is no larger
     * than the answer.
     */
    public static ExactParts times(ExactParts a, ExactParts b) {
        ExactParts inLongs = timesInLongs(a, b);
        return inLongs != null ? inLongs : timesAtAnyWidth(a, b);
    }

    /**
     * {@link #times}, worked out in longs where every number on the way is one the long route holds,
     * and null where one is not or where the exponents are past sixty-four bits. The same parts as
     * {@link #timesAtAnyWidth}, by the same steps: nearly every product the constraint algebra makes
     * is of small fractions, and a {@code BigInteger} answers each step with a new one.
     *
     * <p>Null is not a refusal. A product whose working the long route does not hold is worked out
     * at any width, and that is what refuses where the product has no representation.
     */
    static ExactParts timesInLongs(ExactParts a, ExactParts b) {
        if (a.isZero() || b.isZero() || !inLongs(a) || !inLongs(b)) {
            return null;
        }
        if (!addedInALong(a.twos(), b.twos()) || !addedInALong(a.fives(), b.fives())) {
            return null;
        }
        return crossed(a.numeratorInALong(), a.denominatorInALong(),
                b.numeratorInALong(), b.denominatorInALong(),
                a.twos() + b.twos(), a.fives() + b.fives());
    }

    /**
     * {@code above / below × aboveToo / belowToo} with the exponents given, each fraction's
     * numerator reduced by the other's denominator before anything is multiplied, as a product and
     * a quotient both take it; or null where a product of the two is past the long route.
     */
    private static ExactParts crossed(long above, long below, long aboveToo, long belowToo,
                                      long twos, long fives) {
        long acrossOne = commonFactor(Math.abs(above), Math.abs(belowToo));
        long acrossTwo = commonFactor(Math.abs(aboveToo), Math.abs(below));
        long numeratorOne = above / acrossOne;
        long numeratorTwo = aboveToo / acrossTwo;
        long denominatorOne = below / acrossTwo;
        long denominatorTwo = belowToo / acrossOne;
        if (!multipliesInALong(numeratorOne, numeratorTwo)
                || !multipliesInALong(denominatorOne, denominatorTwo)) {
            return null;
        }
        return new ExactParts(numeratorOne * numeratorTwo, denominatorOne * denominatorTwo,
                twos, fives);
    }

    /** {@link #times}, in whole numbers of whatever size the operands are. */
    static ExactParts timesAtAnyWidth(ExactParts a, ExactParts b) {
        if (a.isZero() || b.isZero()) {
            return ExactParts.ZERO;
        }
        BigInteger acrossOne = commonFactor(a.numerator(), b.denominator());
        BigInteger acrossTwo = commonFactor(b.numerator(), a.denominator());
        try {
            return new ExactParts(
                    a.numerator().divide(acrossOne).multiply(b.numerator().divide(acrossTwo)),
                    a.denominator().divide(acrossTwo).multiply(b.denominator().divide(acrossOne)),
                    ExactPowers.added(a.twos(), b.twos()),
                    ExactPowers.added(a.fives(), b.fives()));
        } catch (ArithmeticException e) {
            throw ExactPowers.hostLimit(e);
        }
    }

    /**
     * The quotient. The exponents subtract and are never built, and the cross factors come off before the
     * multiplication, as they do for the product.
     *
     * <p>Not one over the divisor, multiplied in. A reciprocal's exponents are the divisor's negated, and
     * the least long has no positive counterpart, so a quotient reached that way refused pairs whose own
     * exponents are the difference of two held ones, with {@code r / r} among them. The difference is what
     * the answer's exponents are, so it is what is computed.
     *
     * @throws IllegalArgumentException where the divisor is nought
     */
    public static ExactParts dividedBy(ExactParts a, ExactParts b) {
        ExactParts inLongs = dividedByInLongs(a, b);
        return inLongs != null ? inLongs : dividedByAtAnyWidth(a, b);
    }

    /**
     * {@link #dividedBy}, worked out in longs as {@link #timesInLongs} works out the product, and
     * null where it is not. A divisor's sign stays on the denominator handed back, as it does at any
     * width, and a nought on either side is left to that as well, which says what each one means.
     */
    static ExactParts dividedByInLongs(ExactParts a, ExactParts b) {
        if (a.isZero() || b.isZero() || !inLongs(a) || !inLongs(b)) {
            return null;
        }
        if (!lessenedInALong(a.twos(), b.twos()) || !lessenedInALong(a.fives(), b.fives())) {
            return null;
        }
        // The divisor turned over: its denominator above the line and its numerator, with its
        // sign, below it.
        return crossed(a.numeratorInALong(), a.denominatorInALong(),
                b.denominatorInALong(), b.numeratorInALong(),
                a.twos() - b.twos(), a.fives() - b.fives());
    }

    /** {@link #dividedBy}, in whole numbers of whatever size the operands are. */
    static ExactParts dividedByAtAnyWidth(ExactParts a, ExactParts b) {
        if (b.isZero()) {
            throw new IllegalArgumentException("nought divides nothing");
        }
        if (a.isZero()) {
            return ExactParts.ZERO;
        }
        BigInteger acrossOne = commonFactor(a.numerator(), b.numerator());
        BigInteger acrossTwo = commonFactor(a.denominator(), b.denominator());
        try {
            return new ExactParts(
                    a.numerator().divide(acrossOne).multiply(b.denominator().divide(acrossTwo)),
                    a.denominator().divide(acrossTwo).multiply(b.numerator().divide(acrossOne)),
                    ExactPowers.lessened(a.twos(), b.twos()),
                    ExactPowers.lessened(a.fives(), b.fives()));
        } catch (ArithmeticException e) {
            throw ExactPowers.hostLimit(e);
        }
    }

    /**
     * One over the value, whose exponents are the value's negated.
     *
     * @throws IllegalArgumentException where the value is nought, which has no reciprocal
     * @throws ExactRangeExceeded where an exponent is the least long, which has no negation
     */
    public static ExactParts reciprocal(ExactParts of) {
        if (of.isZero()) {
            throw new IllegalArgumentException("nought has no reciprocal");
        }
        long twos = ExactPowers.negated(of.twos());
        long fives = ExactPowers.negated(of.fives());
        return of.inLongs() ? new ExactParts(of.denominatorInALong(), of.numeratorInALong(), twos, fives)
                : new ExactParts(of.denominator(), of.numerator(), twos, fives);
    }

    /**
     * The sum of {@code terms}: one answer for the terms in whatever order they come, refused only
     * where the sum itself has no representation or this run has no room to form it.
     *
     * <p>A run of {@link #plus} where that is held, and no more than that where it is not. Each of
     * those answers in canonical form, which moves the factors of two and five of its sum into the
     * exponents and refuses an exponent past sixty-four bits — so a run of them asks every partial
     * sum to be representable, and two terms at the greatest exponent fail where they meet even
     * where the next two cancel them. And each of them aligns its two terms, so a fine term and an
     * ordinary one fail where they meet even where a third cancels the fine one. A run that is held
     * is the exact sum whatever order it took, so it is the answer; a run that fails is not, and
     * the sum is made again by scale.
     *
     * <p>Made by scale, nothing in between is put in canonical form. A partial sum is a fraction standing at
     * the exponents of the terms it was made of, the lesser of each, which are exponents some term
     * already has; the one canonical form made is the answer's, so the range is asked of the answer
     * and of nothing else. And the terms meet by scale: terms of one scale first, which align
     * nothing, then the two nearest in scale, so a cancellation is made before anything is aligned
     * across it. What is aligned is then what the answer itself spans, or what is left once every
     * term that could cancel has.
     *
     * @throws ExactRangeExceeded where the sum has no representation, or the terms left span more
     *                            than a whole number the host holds
     */
    public static ExactParts sum(Iterable<ExactParts> terms) {
        // The terms as they come first, which is the whole of nearly every sum: an exact sum that
        // is held is the sum, whatever order made it. Only a sum that fails this way can turn on the
        // order, so only that one is made again by scale.
        try {
            ExactParts total = ExactParts.ZERO;
            for (ExactParts each : terms) {
                total = total.isZero() ? each : plus(total, each);
            }
            return canonical(total);
        } catch (ExactFailure _) {
            return byScale(terms, SumWork.NOBODY_PAYS);
        }
    }

    /**
     * The same sum, made by scale from the first, with {@code work} told what each piece of it
     * costs before the piece is done — for a caller paying for what it does, to whom what the sum
     * costs is as much its answer as the sum.
     *
     * <p>So what it costs is the terms' and not their order's. The terms are walked twice and never
     * gathered: once for how much each scale holds, and once to add them up. Each term added at its
     * scale is told with what every term of that scale holds together, which no partial sum of
     * them is longer than whichever came first; each meeting of two scales is of partial sums that
     * are each the exact sum of their scale's terms, in lowest terms, so the same whatever order
     * they came in; and which two meet is the nearest pair, which the scales decide. A run of
     * {@link #plus} first, as {@link #sum(Iterable)} makes, would cost what the order makes it —
     * a fine term and an ordinary one aligned before the fine term's negation cancels it.
     *
     * @throws ExactRangeExceeded as {@link #sum(Iterable)} does
     */
    public static ExactParts sumByScale(Iterable<ExactParts> terms, SumWork work) {
        return byScale(terms, work);
    }

    /**
     * What a sum made by scale costs, told piece by piece before each piece is done
     * ({@link #sumByScale}).
     */
    public interface SumWork {

        /** Work nobody pays for. */
        SumWork NOBODY_PAYS = new SumWork() {

            @Override
            public void atOneScale(ExactParts term, long numeratorAtMost, long denominatorAtMost) {
            }

            @Override
            public void across(ExactParts one, ExactParts other) {
            }
        };

        /**
         * {@code term} added into the partial sum of its scale, which aligns nothing.
         *
         * <p>Told with how long a partial sum of that scale can be, whichever of its terms came
         * first: a denominator no longer than every term's denominator multiplied together, and a
         * numerator no longer than the longest numerator multiplied up to that denominator and
         * carried once for each term. Of decimals, whose denominators are one, that is the longest
         * of them and a carry — not every term's length together.
         *
         * @param numeratorAtMost   the bits no partial numerator of the scale holds more of
         * @param denominatorAtMost the bits no partial denominator of the scale holds more of
         */
        void atOneScale(ExactParts term, long numeratorAtMost, long denominatorAtMost);

        /** Two partial sums of different scales added, aligned at the lesser of each exponent. */
        void across(ExactParts one, ExactParts other);
    }

    /** {@link #sumByScale} made: no partial sum in canonical form, terms of one scale first and
     *  then the two nearest in scale. */
    private static ExactParts byScale(Iterable<ExactParts> terms, SumWork work) {
        try {
            // How long a partial sum of each scale can be, read off the terms without adding any.
            NavigableMap<Scale, Holds> holds = new TreeMap<>();
            for (ExactParts each : terms) {
                if (!each.isZero()) {
                    holds.merge(Scale.of(each), Holds.of(each), Holds::and);
                }
            }
            // Terms of one scale, as one fraction at that scale each. Exact, so it is the same
            // fraction whichever of them came first.
            NavigableMap<Scale, ExactParts> at = new TreeMap<>();
            for (ExactParts each : terms) {
                if (!each.isZero()) {
                    Scale scale = Scale.of(each);
                    Holds scaleHolds = holds.get(scale);
                    work.atOneScale(each, scaleHolds.numeratorAtMost(),
                            scaleHolds.denominatorAtMost());
                    at.merge(scale, each, ExactArithmetic::aligned);
                }
            }
            at.values().removeIf(ExactParts::isZero);
            ExactParts only = new NearestFirst(at, work).met();
            return only == null ? ExactParts.ZERO : canonical(only);
        } catch (ArithmeticException e) {
            throw ExactPowers.hostLimit(e);
        }
    }

    /**
     * What the terms of one scale hold: how many there are, the longest numerator, and the bits
     * their denominators multiplied together hold beyond one.
     */
    private record Holds(long count, long longestNumerator, long denominators) {

        static Holds of(ExactParts term) {
            return new Holds(1, term.numerator().bitLength(), term.denominator().bitLength() - 1L);
        }

        Holds and(Holds other) {
            return new Holds(saturated(count, other.count),
                    Math.max(longestNumerator, other.longestNumerator),
                    saturated(denominators, other.denominators));
        }

        /** No partial denominator of the scale is longer than every denominator multiplied. */
        long denominatorAtMost() {
            return saturated(denominators, 1);
        }

        /** No partial numerator is longer than the longest raised to that denominator, carried
         *  once for each term. */
        long numeratorAtMost() {
            return saturated(saturated(longestNumerator, denominatorAtMost()),
                    Long.SIZE - Long.numberOfLeadingZeros(count));
        }
    }

    private static long saturated(long a, long b) {
        try {
            return Math.addExact(a, b);
        } catch (ArithmeticException _) {
            return Long.MAX_VALUE;
        }
    }

    /**
     * Partial sums of distinct scales met two at a time, the two nearest in scale first — the first
     * such pair in the order of scales where several are as near — until one is left.
     *
     * <p>Each scale keeps which other is nearest to it, and the nearest pair of all is the least
     * of those. A meeting asks again only of the ones it touched — the scale the two met at, and
     * any whose nearest was one of the two — since how far apart two scales are is the same either
     * way: a scale's nearest is never made wrong by a sum made somewhere else, only beaten, and the
     * new scale's own nearest says that. Which scale is nearest is asked of the scales at the
     * powers of two near its own and not of all of them. Kept in trees and in no array, since how many scales there
     * are is as many as the terms.
     */
    private static final class NearestFirst {

        private final NavigableMap<Scale, ExactParts> at;
        private final SumWork work;
        /** The scales still here, as the powers of five each power of two stands with. */
        private final NavigableMap<Long, NavigableSet<Long>> byTwos = new TreeMap<>();
        /** Each scale's nearest, least first. */
        private final NavigableSet<Pair> pairs = new TreeSet<>();
        private final NavigableMap<Scale, Pair> nearestOf = new TreeMap<>();
        /** Which scales each scale is the nearest of. */
        private final NavigableMap<Scale, NavigableSet<Scale>> nearestTo = new TreeMap<>();

        /** A scale and the scale nearest it, ordered by how far apart and then by the scales. */
        private record Pair(long apart, Scale one, Scale other) implements Comparable<Pair> {

            @Override
            public int compareTo(Pair that) {
                int byApart = Long.compare(apart, that.apart);
                if (byApart != 0) {
                    return byApart;
                }
                int byOne = one.compareTo(that.one);
                return byOne != 0 ? byOne : other.compareTo(that.other);
            }
        }

        /**
         * The partial sums to meet, each with which other is nearest to it.
         *
         * @param at the partial sums by their scales, none of them nought
         */
        NearestFirst(NavigableMap<Scale, ExactParts> at, SumWork work) {
            this.at = at;
            this.work = work;
            for (Scale each : at.keySet()) {
                byTwos.computeIfAbsent(each.twos(), _ -> new TreeSet<>()).add(each.fives());
            }
            for (Scale each : at.keySet()) {
                findNearest(each);
            }
        }

        /** What is left once every term has met, or null where they came to nought. */
        ExactParts met() {
            while (at.size() > 1) {
                Pair nearest = pairs.first();
                Scale first = nearest.one().compareTo(nearest.other()) < 0
                        ? nearest.one() : nearest.other();
                Scale second = first.equals(nearest.one()) ? nearest.other() : nearest.one();
                work.across(at.get(first), at.get(second));
                ExactParts sum = aligned(at.get(first), at.get(second));
                NavigableSet<Scale> asked = new TreeSet<>();
                remove(first, asked);
                remove(second, asked);
                if (!sum.isZero()) {
                    // What two scales meet at is the lesser of each exponent, which may be a scale
                    // a third term already stands at: that one is nearest of all, at no distance.
                    Scale made = Scale.of(sum);
                    ExactParts there = at.get(made);
                    if (there != null) {
                        work.across(there, sum);
                        sum = aligned(there, sum);
                        remove(made, asked);
                    }
                    if (!sum.isZero()) {
                        at.put(made, sum);
                        byTwos.computeIfAbsent(made.twos(), _ -> new TreeSet<>()).add(made.fives());
                        asked.add(made);
                    }
                }
                for (Scale each : asked) {
                    if (at.containsKey(each)) {
                        findNearest(each);
                    }
                }
            }
            return at.isEmpty() ? null : at.firstEntry().getValue();
        }

        /** {@code scale} gone, and every scale whose nearest it was put in {@code asked}. */
        private void remove(Scale scale, NavigableSet<Scale> asked) {
            at.remove(scale);
            NavigableSet<Long> withTwos = byTwos.get(scale.twos());
            withTwos.remove(scale.fives());
            if (withTwos.isEmpty()) {
                byTwos.remove(scale.twos());
            }
            forgetNearestOf(scale);
            NavigableSet<Scale> pointing = nearestTo.remove(scale);
            if (pointing != null) {
                asked.addAll(pointing);
            }
        }

        private void forgetNearestOf(Scale scale) {
            Pair was = nearestOf.remove(scale);
            if (was != null) {
                pairs.remove(was);
                NavigableSet<Scale> pointing = nearestTo.get(was.other());
                if (pointing != null) {
                    pointing.remove(scale);
                }
            }
        }

        /**
         * Which scale still here is nearest to {@code scale}, the first in their order where
         * several are as near — asked of each power of two outward from its own until one is
         * farther than the nearest found.
         */
        private void findNearest(Scale scale) {
            forgetNearestOf(scale);
            Nearest found = new Nearest(scale);
            found.along(byTwos.tailMap(scale.twos(), true));
            found.along(byTwos.headMap(scale.twos(), false).descendingMap());
            if (found.best != null) {
                Pair pair = new Pair(found.apart, scale, found.best);
                pairs.add(pair);
                nearestOf.put(scale, pair);
                nearestTo.computeIfAbsent(found.best, _ -> new TreeSet<>()).add(scale);
            }
        }

        /** The nearest scale to {@code of} found so far, looked for one power of two at a time. */
        private static final class Nearest {

            private final Scale of;
            private Scale best;
            private long apart = Long.MAX_VALUE;

            Nearest(Scale of) {
                this.of = of;
            }

            /** The powers of two of {@code side}, walked away from {@code of}'s own, until one is
             *  farther than the nearest found. */
            void along(NavigableMap<Long, NavigableSet<Long>> side) {
                for (Map.Entry<Long, NavigableSet<Long>> withTwos : side.entrySet()) {
                    long twosApart = distance(withTwos.getKey(), of.twos());
                    if (best != null && twosApart > apart) {
                        return;
                    }
                    boolean own = withTwos.getKey() == of.twos();
                    NavigableSet<Long> fives = withTwos.getValue();
                    consider(withTwos.getKey(), twosApart,
                            own ? fives.lower(of.fives()) : fives.floor(of.fives()));
                    consider(withTwos.getKey(), twosApart,
                            own ? fives.higher(of.fives()) : fives.ceiling(of.fives()));
                }
            }

            private void consider(long twos, long twosApart, Long fives) {
                if (fives == null) {
                    return;
                }
                Scale there = new Scale(twos, fives);
                long here = saturated(twosApart, distance(fives, of.fives()));
                if (best == null || here < apart || (here == apart && there.compareTo(best) < 0)) {
                    best = there;
                    apart = here;
                }
            }
        }

        /** How far apart two exponents are; the farthest a long holds stands for any farther. */
        private static long distance(long a, long b) {
            try {
                return Math.absExact(Math.subtractExact(a, b));
            } catch (ArithmeticException _) {
                return Long.MAX_VALUE;
            }
        }
    }

    /** The powers of two and five a term stands at, which is what a sum aligns. */
    private record Scale(long twos, long fives) implements Comparable<Scale> {

        static Scale of(ExactParts parts) {
            return new Scale(parts.twos(), parts.fives());
        }

        @Override
        public int compareTo(Scale other) {
            int byTwos = Long.compare(twos, other.twos);
            return byTwos != 0 ? byTwos : Long.compare(fives, other.fives);
        }
    }

    /**
     * Two partial sums added at the lesser of each exponent, which some term has, and left in no
     * canonical form: the factors of two and five the fraction comes to stay in it, so no exponent
     * is moved and none can leave its range here. At one scale nothing is aligned.
     */
    private static ExactParts aligned(ExactParts a, ExactParts b) {
        long commonTwos = Math.min(a.twos(), b.twos());
        long commonFives = Math.min(a.fives(), b.fives());
        BigInteger here = a.numerator().multiply(ExactPowers.powers(
                ExactPowers.lessened(a.twos(), commonTwos),
                ExactPowers.lessened(a.fives(), commonFives)));
        BigInteger there = b.numerator().multiply(ExactPowers.powers(
                ExactPowers.lessened(b.twos(), commonTwos),
                ExactPowers.lessened(b.fives(), commonFives)));
        // The denominators' common factor off before either is multiplied out, and the sum's
        // common factor with its denominator after, so the fraction is no larger than it is.
        BigInteger shared = commonFactor(a.denominator(), b.denominator());
        BigInteger overA = a.denominator().divide(shared);
        BigInteger overB = b.denominator().divide(shared);
        BigInteger sum = here.multiply(overB).add(there.multiply(overA));
        BigInteger denominator = overA.multiply(b.denominator());
        BigInteger common = commonFactor(sum, denominator);
        if (common.signum() != 0 && !common.equals(BigInteger.ONE)) {
            sum = sum.divide(common);
            denominator = denominator.divide(common);
        }
        return new ExactParts(sum, denominator, commonTwos, commonFives);
    }

    /**
     * The sum.
     *
     * <p>The lesser of each pair of exponents is common to both terms and stays an exponent. What is left
     * is the distance between them, and that is built: the exact sum of two values whose exponents are far
     * apart is a number with that many digits in it, and no representation of the answer is smaller than
     * the answer.
     *
     * <p>The denominators' common factor is taken off before either is multiplied out, so the intermediate
     * is the size of the result rather than of the product of the two denominators. The sum is the one
     * operation that forms a number larger than its answer, and it is the one whose formed number is not a
     * route to the answer but the answer's own definition: what cancels in an exact sum is visible only
     * once the terms are over a common denominator. So a pair of stored fractions near the host's own end
     * has no sum, and that is a limit of the operation and not a limit of the machine.
     */
    public static ExactParts plus(ExactParts a, ExactParts b) {
        ExactParts inLongs = plusInLongs(a, b);
        return inLongs != null ? inLongs : plusAtAnyWidth(a, b);
    }

    /**
     * {@link #plus}, worked out in longs where every number on the way is one the long route holds,
     * and null where one is not. The same parts as {@link #plusAtAnyWidth}, by the same steps: the
     * terms raised to the lesser of each exponent, the denominators' common factor off, and the sum
     * formed with its factors of two taken off as {@link #summed} takes them.
     *
     * <p>Null is not a refusal, here least of all. A sum whose working is past a long can still come
     * to an ordinary value, and the arithmetic at any width is what forms it, or refuses where the
     * sum has no representation.
     */
    static ExactParts plusInLongs(ExactParts a, ExactParts b) {
        if (a.isZero() || b.isZero() || !inLongs(a) || !inLongs(b)) {
            return null;
        }
        long commonTwos = Math.min(a.twos(), b.twos());
        long commonFives = Math.min(a.fives(), b.fives());
        long here = raised(a.numeratorInALong(),
                a.twos() - commonTwos, a.fives() - commonFives);
        long there = raised(b.numeratorInALong(),
                b.twos() - commonTwos, b.fives() - commonFives);
        if (here == 0 || there == 0) {
            return null;
        }
        long aDenominator = a.denominatorInALong();
        long bDenominator = b.denominatorInALong();
        long shared = commonFactor(Math.abs(aDenominator), Math.abs(bDenominator));
        long overThis = aDenominator / shared;
        long overThat = bDenominator / shared;
        if (!multipliesInALong(here, overThat) || !multipliesInALong(there, overThis)
                || !multipliesInALong(overThis, bDenominator)) {
            return null;
        }
        // Each of a magnitude below two to the sixty-two, so their sum is held whatever their
        // signs, and so is the halving of each below.
        long one = here * overThat;
        long other = there * overThis;
        long whole;
        int twos;
        if (Long.signum(one) != Long.signum(other)) {
            whole = one + other;
            twos = 0;
        } else {
            int common = Math.min(Long.numberOfTrailingZeros(one),
                    Long.numberOfTrailingZeros(other));
            one >>= common;
            other >>= common;
            if ((one & 1) != 0 && (other & 1) != 0) {
                whole = (one >> 1) + (other >> 1) + 1;
                twos = common + 1;
            } else {
                whole = one + other;
                twos = common;
            }
        }
        if (!addedInALong(commonTwos, twos)) {
            return null;
        }
        return new ExactParts(whole, overThis * bDenominator, commonTwos + twos, commonFives);
    }

    /** {@link #plus}, in whole numbers of whatever size the operands are. */
    static ExactParts plusAtAnyWidth(ExactParts a, ExactParts b) {
        if (a.isZero()) {
            return b;
        }
        if (b.isZero()) {
            return a;
        }
        long commonTwos = Math.min(a.twos(), b.twos());
        long commonFives = Math.min(a.fives(), b.fives());
        try {
            BigInteger here = a.numerator().multiply(ExactPowers.powers(
                    ExactPowers.lessened(a.twos(), commonTwos),
                    ExactPowers.lessened(a.fives(), commonFives)));
            BigInteger there = b.numerator().multiply(ExactPowers.powers(
                    ExactPowers.lessened(b.twos(), commonTwos),
                    ExactPowers.lessened(b.fives(), commonFives)));
            BigInteger shared = commonFactor(a.denominator(), b.denominator());
            BigInteger overThis = a.denominator().divide(shared);
            Summed sum = summed(
                    here.multiply(b.denominator().divide(shared)), there.multiply(overThis));
            return new ExactParts(sum.whole(), overThis.multiply(b.denominator()),
                    ExactPowers.added(commonTwos, sum.twos()), commonFives);
        } catch (ArithmeticException e) {
            throw ExactPowers.hostLimit(e);
        }
    }

    /** A sum, and the factors of two taken off it while it was formed. */
    record Summed(BigInteger whole, int twos) {}

    /**
     * The sum of two whole numbers, with its factors of two taken off as it is formed rather than after.
     *
     * <p>The host holds a largest whole number, and two numbers it holds can have a sum wanting one bit
     * more — while the value that sum stands for holds that bit as an exponent and is an ordinary one. So
     * where the sum is even what is formed is its odd part, and the factors of two go where every other
     * factor of two goes.
     *
     * <p>Only the factors of two, and so only the sums whose extra bit is one of those. A sum of two odd
     * numbers is even and is the shape a carry takes when neither side can give a bit back; a sum with one
     * side odd is odd, and is as large as it is going to be. What that leaves is a sum of a size the host
     * holds or a sum that has no representation at all, except where the extra bit would have come off as
     * a five instead — which is not taken off, five having no halving that leaves both sides where they
     * are.
     *
     * <p>Neither side has to be made larger to halve their sum. Where both are even, both come down; where
     * both are odd, {@code (a + b) / 2} is {@code a/2 + b/2 + 1}, which holds for two negatives as well,
     * the halving being the one that rounds down on both.
     */
    static Summed summed(BigInteger a, BigInteger b) {
        if (a.signum() != b.signum()) {
            // The magnitudes take away from one another, so the sum is no larger than the greater of them.
            return new Summed(a.add(b), 0);
        }
        int common = Math.min(a.getLowestSetBit(), b.getLowestSetBit());
        BigInteger here = a.shiftRight(common);
        BigInteger there = b.shiftRight(common);
        if (here.testBit(0) && there.testBit(0)) {
            return new Summed(
                    here.shiftRight(1).add(there.shiftRight(1)).add(BigInteger.ONE), common + 1);
        }
        return new Summed(here.add(there), common);
    }

    /**
     * Where {@code a} stands against {@code b} by exact mathematical value.
     *
     * <p>Answered for every pair, and answered by equality of parts where they are equal, which one
     * canonical form per value makes the whole of it.
     *
     * @throws ExactRoomExceeded where this run has no room for the working width the pair needs
     */
    public static int compare(ExactParts a, ExactParts b) {
        return compare(a, b, ExactOrder.NOBODY_ASKS);
    }

    /**
     * {@link #compare(ExactParts, ExactParts)}, telling {@code widened} the width, in bits, of each
     * bracket the order is refined at before it is taken. How many there are turns on how closely the
     * two values agree and not on anything a caller can see beforehand, so a caller paying for the
     * work pays for these as they come.
     */
    public static int compare(ExactParts a, ExactParts b, LongConsumer widened) {
        if (a.equals(b)) {
            return 0;
        }
        int bySign = Integer.compare(a.signum(), b.signum());
        if (bySign != 0) {
            return bySign;
        }
        // Only where nobody counts the brackets: a pair this settles can be one the brackets refine,
        // and a caller paying for each bracket pays for the work the order takes at any width.
        int byMagnitude = widened == ExactOrder.NOBODY_ASKS ? magnitudesInLongs(a, b) : UNDECIDED;
        if (byMagnitude == UNDECIDED) {
            byMagnitude = ExactOrder.magnitudes(a, b, widened);
        }
        return a.signum() > 0 ? byMagnitude : -byMagnitude;
    }

    /** What {@link #magnitudesInLongs} answers where the long route does not hold the pair. */
    static final int UNDECIDED = 2;

    /** The widest exponent whose difference from another is read as a long without checking. */
    private static final long NEAR = 1L << 31;

    /** Whether {@code exponent} is within {@link #NEAR} of nought — asked of its two ends and not of
     *  its magnitude, which the least long has none of. */
    private static boolean near(long exponent) {
        return exponent >= -NEAR && exponent <= NEAR;
    }

    /**
     * Where the magnitude of {@code a} stands against that of {@code b}, by cross-multiplying longs,
     * or {@link #UNDECIDED} where the numbers do not fit them.
     *
     * <p>The order of {@code |n₁|·d₂·2^t₁·5^f₁} against {@code |n₂|·d₁·2^t₂·5^f₂}: dividing both by the
     * lesser power of each prime leaves only the differences of the exponents, and where the side
     * those raise is held by a long, each side is a product of two longs below two to the sixty-three,
     * compared as the hundred and twenty-eight bits it is. So every long but the least is taken, and
     * the numbers that bound an {@code Int} are ordered against ordinary ones without a bracket.
     */
    static int magnitudesInLongs(ExactParts a, ExactParts b) {
        if (!a.inLongs() || !b.inLongs()
                || a.numeratorInALong() == Long.MIN_VALUE || b.numeratorInALong() == Long.MIN_VALUE
                || a.denominatorInALong() <= 0 || b.denominatorInALong() <= 0
                || !near(a.twos()) || !near(b.twos()) || !near(a.fives()) || !near(b.fives())) {
            return UNDECIDED;
        }
        long twosApart = a.twos() - b.twos();
        long fivesApart = a.fives() - b.fives();
        long mine = raisedUnlessByNothing(Math.abs(a.numeratorInALong()), Math.max(twosApart, 0),
                Math.max(fivesApart, 0));
        long theirs = raisedUnlessByNothing(Math.abs(b.numeratorInALong()), Math.max(-twosApart, 0),
                Math.max(-fivesApart, 0));
        if (mine == 0 || theirs == 0) {
            return UNDECIDED;
        }
        long mineOver = b.denominatorInALong();
        long theirsOver = a.denominatorInALong();
        int byHigh = Long.compare(Math.multiplyHigh(mine, mineOver), Math.multiplyHigh(theirs, theirsOver));
        return byHigh != 0 ? byHigh : Long.compareUnsigned(mine * mineOver, theirs * theirsOver);
    }

    /** {@code whole} itself where it is raised by no power, and {@link #raised} where it is. */
    private static long raisedUnlessByNothing(long whole, long twos, long fives) {
        return twos == 0 && fives == 0 ? whole : raised(whole, twos, fives);
    }

    /**
     * The whole number {@code of × 10^scale} rounds to by {@code towards}, which is the unscaled value of
     * the value at that scale.
     *
     * @throws IllegalArgumentException where the value is not a whole number at that scale and the policy
     *         is {@link RoundingMode#UNNECESSARY}
     */
    public static BigInteger roundedTimesTenTo(ExactParts of, int scale, RoundingMode towards) {
        return ExactRounding.roundedTimesTenTo(of, scale, towards, ExactOrder.NOBODY_ASKS);
    }

    /** {@link #roundedTimesTenTo(ExactParts, int, RoundingMode)}, telling {@code widened} the width of
     *  each bracket the rounding is refined at, as {@link #compare(ExactParts, ExactParts, LongConsumer)}
     *  does. */
    public static BigInteger roundedTimesTenTo(ExactParts of, int scale, RoundingMode towards,
                                               LongConsumer widened) {
        return ExactRounding.roundedTimesTenTo(of, scale, towards, widened);
    }

    /**
     * {@code whole × 2^twos × 5^fives} written out, both exponents being at least nought.
     *
     * <p>The one place a power is built, so the one place it is refused, and refused on sight.
     *
     * @throws ExactRangeExceeded where no whole number the host holds is that number
     */
    public static BigInteger written(BigInteger whole, BigInteger twos, BigInteger fives) {
        return ExactPowers.built(whole, twos, fives);
    }

    /**
     * Whether {@link #written} would answer, without building the number: whether the host holds
     * {@code whole × 2^twos × 5^fives}.
     *
     * <p>The same count the building asks, so a caller deciding whether a value can be written and the
     * writing of it never disagree.
     */
    public static boolean canBeWritten(BigInteger whole, BigInteger twos, BigInteger fives) {
        return ExactPowers.writable(whole, twos, fives);
    }

    /** {@link #canBeWritten(BigInteger, BigInteger, BigInteger)} of the numerator of {@code parts},
     *  with two exponents at or above nought that a long holds. */
    public static boolean canBeWritten(ExactParts parts, long twos, long fives) {
        return ExactPowers.writable(parts.numeratorMagnitudeBits(), twos, fives);
    }

    /** An exponent negated, which the least long is not. */
    public static long negated(long exponent) {
        return ExactPowers.negated(exponent);
    }

    /**
     * What an exponent stands for above the line: the exponent where it is above nought, and nought
     * where it is not.
     *
     * <p>Held wider than a long, as is {@link #belowTheLine}, so that no caller reads an exponent's
     * negation as a {@code long}: the least long has none, and a negation that wrapped would say nought.
     */
    public static BigInteger aboveTheLine(long exponent) {
        return BigInteger.valueOf(exponent).max(BigInteger.ZERO);
    }

    /** What an exponent stands for below the line: its negation where it is below nought, and nought
     *  where it is not. For the least long that is a power of two no long holds. */
    public static BigInteger belowTheLine(long exponent) {
        return BigInteger.valueOf(exponent).negate().max(BigInteger.ZERO);
    }
}
