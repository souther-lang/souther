package souther.exact;

import java.math.BigInteger;
import java.math.RoundingMode;

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
        BigInteger common = numerator.gcd(denominator);
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
        // A five leaves no such mark, so it is one division each — bounded by the digits the number
        // already has, so nothing here is amplified by the exponents: a power of ten held as a scale never
        // reaches this loop at all.
        while (true) {
            BigInteger[] divided = numerator.divideAndRemainder(ExactPowers.FIVE);
            if (divided[1].signum() != 0) {
                break;
            }
            numerator = divided[0];
            fives = ExactPowers.added(fives, 1);
        }
        while (true) {
            BigInteger[] divided = denominator.divideAndRemainder(ExactPowers.FIVE);
            if (divided[1].signum() != 0) {
                break;
            }
            denominator = divided[0];
            fives = ExactPowers.added(fives, -1);
        }
        return new ExactParts(numerator, denominator, twos, fives);
    }

    /**
     * The product. The exponents add and are never built, and the common factors of the two fractions are
     * taken off before the numerators and denominators are multiplied, so what is multiplied is no larger
     * than the answer.
     */
    public static ExactParts times(ExactParts a, ExactParts b) {
        if (a.isZero() || b.isZero()) {
            return ExactParts.ZERO;
        }
        BigInteger acrossOne = a.numerator().gcd(b.denominator());
        BigInteger acrossTwo = b.numerator().gcd(a.denominator());
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
        if (b.isZero()) {
            throw new IllegalArgumentException("nought divides nothing");
        }
        if (a.isZero()) {
            return ExactParts.ZERO;
        }
        BigInteger acrossOne = a.numerator().gcd(b.numerator());
        BigInteger acrossTwo = a.denominator().gcd(b.denominator());
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
        return new ExactParts(of.denominator(), of.numerator(),
                ExactPowers.negated(of.twos()), ExactPowers.negated(of.fives()));
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
            BigInteger shared = a.denominator().gcd(b.denominator());
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
        if (a.equals(b)) {
            return 0;
        }
        int bySign = Integer.compare(a.signum(), b.signum());
        if (bySign != 0) {
            return bySign;
        }
        int byMagnitude = ExactOrder.magnitudes(a, b);
        return a.signum() > 0 ? byMagnitude : -byMagnitude;
    }

    /**
     * The whole number {@code of × 10^scale} rounds to by {@code towards}, which is the unscaled value of
     * the value at that scale.
     *
     * @throws IllegalArgumentException where the value is not a whole number at that scale and the policy
     *         is {@link RoundingMode#UNNECESSARY}
     */
    public static BigInteger roundedTimesTenTo(ExactParts of, int scale, RoundingMode towards) {
        return ExactRounding.roundedTimesTenTo(of, scale, towards);
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

    /** {@code 2^twos × 5^fives} written out, both exponents being at least nought. */
    public static BigInteger written(long twos, long fives) {
        return ExactPowers.powers(twos, fives);
    }

    /** An exponent negated, which the least long is not. */
    public static long negated(long exponent) {
        return ExactPowers.negated(exponent);
    }
}
