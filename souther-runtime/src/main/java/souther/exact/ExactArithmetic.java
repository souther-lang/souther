package souther.exact;

import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.Map;
import java.util.NavigableMap;
import java.util.NavigableSet;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.BiConsumer;
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
        if (numerator.bitLength() < Long.SIZE - 1 && denominator.bitLength() < Long.SIZE - 1) {
            return canonical(numerator.longValue(), denominator.longValue(), twos, fives);
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
     * The same canonical form, of a numerator and a positive denominator a long holds with a bit to
     * spare, worked out in longs.
     *
     * <p>Nearly every value the constraint algebra and a model's rationals make is this small, and
     * the steps are the ones above: the common factor off, then the twos where the bits stop, then
     * the fives one division each. In longs none of them allocates, where each division of a
     * {@code BigInteger} answers a new one, and a remainder check answers two. The spare bit is what
     * lets the magnitude of the numerator be taken without the least long, which has none.
     */
    private static ExactParts canonical(long numerator, long denominator, long twos, long fives) {
        long common = commonFactor(Math.abs(numerator), denominator);
        numerator /= common;
        denominator /= common;
        int inNumerator = Long.numberOfTrailingZeros(numerator);
        if (inNumerator > 0) {
            numerator >>= inNumerator;
            twos = ExactPowers.added(twos, inNumerator);
        }
        int inDenominator = Long.numberOfTrailingZeros(denominator);
        if (inDenominator > 0) {
            denominator >>= inDenominator;
            twos = ExactPowers.added(twos, -inDenominator);
        }
        while (numerator % 5 == 0) {
            numerator /= 5;
            fives = ExactPowers.added(fives, 1);
        }
        while (denominator % 5 == 0) {
            denominator /= 5;
            fives = ExactPowers.added(fives, -1);
        }
        return new ExactParts(BigInteger.valueOf(numerator), BigInteger.valueOf(denominator),
                twos, fives);
    }

    /** The greatest common factor of two positive longs. */
    private static long commonFactor(long a, long b) {
        while (b != 0) {
            long rest = a % b;
            a = b;
            b = rest;
        }
        return a;
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
        return sum(terms, (one, other) -> { });
    }

    /**
     * {@link #sum(Iterable)}, with {@code meeting} told each two partial sums before they are
     * added — which is the work a caller paying for what it does pays for, one meeting at a time as
     * {@link #plus} would be.
     *
     * <p>A partial sum handed to {@code meeting} is in no canonical form: its exponents are some
     * term's, and the factors of two and five its fraction holds stay in the fraction.
     *
     * <p>The terms are walked and never gathered: what is kept is one partial sum for each scale
     * met, so a sum of as many terms as a collection of the language holds asks for no array of
     * them. They are walked once more where the sum is made by scale.
     */
    public static ExactParts sum(Iterable<ExactParts> terms,
                                 BiConsumer<ExactParts, ExactParts> meeting) {
        // The terms as they come first, which is the whole of nearly every sum: an exact sum that
        // is held is the sum, whatever order made it. Only a sum that fails this way can turn on the
        // order, so only that one is made again by scale.
        try {
            ExactParts total = ExactParts.ZERO;
            for (ExactParts each : terms) {
                if (total.isZero()) {
                    total = each;
                    continue;
                }
                meeting.accept(total, each);
                total = plus(total, each);
            }
            return canonical(total.numerator(), total.denominator(), total.twos(), total.fives());
        } catch (ExactFailure _) {
            return byScale(terms, meeting);
        }
    }

    /** {@link #sum(Iterable, BiConsumer)} made by scale: no partial sum in canonical form, terms of
     *  one scale first and then the two nearest in scale. */
    private static ExactParts byScale(Iterable<ExactParts> terms,
                                      BiConsumer<ExactParts, ExactParts> meeting) {
        try {
            // Terms of one scale, as one fraction at that scale each. Exact, so it is the same
            // fraction whichever of them came first.
            NavigableMap<Scale, ExactParts> at = new TreeMap<>();
            for (ExactParts each : terms) {
                if (!each.isZero()) {
                    at.merge(Scale.of(each), each, (one, other) -> {
                        meeting.accept(one, other);
                        return aligned(one, other);
                    });
                }
            }
            at.values().removeIf(ExactParts::isZero);
            ExactParts only = new NearestFirst(at, meeting).met();
            return only == null ? ExactParts.ZERO
                    : canonical(only.numerator(), only.denominator(), only.twos(), only.fives());
        } catch (ArithmeticException e) {
            throw ExactPowers.hostLimit(e);
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
        private final BiConsumer<ExactParts, ExactParts> meeting;
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
        NearestFirst(NavigableMap<Scale, ExactParts> at, BiConsumer<ExactParts, ExactParts> meeting) {
            this.at = at;
            this.meeting = meeting;
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
                meeting.accept(at.get(first), at.get(second));
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
                        meeting.accept(there, sum);
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

        private static long saturated(long a, long b) {
            try {
                return Math.addExact(a, b);
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
        BigInteger shared = a.denominator().gcd(b.denominator());
        BigInteger overA = a.denominator().divide(shared);
        BigInteger overB = b.denominator().divide(shared);
        BigInteger sum = here.multiply(overB).add(there.multiply(overA));
        BigInteger denominator = overA.multiply(b.denominator());
        BigInteger common = sum.gcd(denominator);
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
        int byMagnitude = ExactOrder.magnitudes(a, b, widened);
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
