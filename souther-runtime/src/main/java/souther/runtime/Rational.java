package souther.runtime;

import org.jspecify.annotations.Nullable;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.function.Supplier;

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
 * <p><b>Why the exponents are sixty-four bits.</b> Every {@code Int} and every {@code Decimal} has one
 * exact value here, and that is a rule rather than a range this type happens to cover (ADR-0116). A
 * {@code Decimal}'s scale is thirty-two bits and enters as its negation, and negating the least
 * thirty-two-bit number leaves it — so an exponent held to a scale's own width would refuse a decimal
 * the widening is supposed to take, and stripping a factor of two out of the numerator would push one
 * more past the end. What a computation can ask for past this width aborts, as an {@code Int}'s
 * overflow does (spec §jvm-abort).
 *
 * <p><b>What the exponents cost.</b> Multiplying and dividing add and subtract them and never build
 * them, so scale stays free across both. Adding does build the difference between two exponents,
 * because that is what the exact sum is: {@code 1 + 1E-1000000} has a million digits whatever holds
 * it. Comparing builds nothing for the pairs a bracket separates, which is nearly all of them: a power
 * of two is a count of bits there and a power of five is bracketed by squaring, so {@code r < 1} does
 * not spell out a millionth. Where a bracket does not separate the pair, the two values are written out
 * as one fraction each and compared exactly, which costs what those fractions cost and is worth doing
 * while it costs about what holding them does; past that the bracket is taken again wider instead, and
 * either way a pair standing closer together than any width settled on beforehand is answered.
 *
 * <p><b>What a step is allowed to refuse.</b> An operation aborts where the answer has no
 * representation here, and not where a step on the way to it has none. The two are easy to confuse
 * because the shapes that separate them are at the ends of the exponent's range, which a run of
 * squarings reaches and an ordinary model does not: a quotient's exponents are the difference of two
 * held ones and a reciprocal's are a negation, so division that went by the reciprocal refused
 * {@code r / r}; a decimal's scale is signed, so a narrowing that took a non-negative one built the
 * power a compact decimal had carried as its scale; a rounding policy is asked for so that a value
 * comes back, so reading it off the digits refused values it was named to answer. Each of those is a
 * middle step narrower than the value it was handed.
 *
 * <p>The order is the case where that rule bites hardest, because an order always exists. So it rests on
 * neither of the two things that would refuse it: not on a precision settled before the pair arrived, two
 * fractions being able to stand closer than any such precision; and not on the powers the two values
 * stand for, the pairs whose logs sit closest together being the ones whose powers are largest. Telling
 * two values apart takes as many bits as they agree over, and a pair may agree over as many as its own
 * fractions have — so a comparison may want working room in proportion to what it was handed. That is what
 * it costs, and not a pair it declines: where the room runs out the run has failed and says so
 * ({@link OutOfRoom}), and the same pair compares where there is more of it. Being ordered is a fact about
 * this type, so what a heap's size may not decide is whether a {@code sort} over these is admitted and what
 * it means — as against whether one run of it finishes, which is what any operation is subject to.
 *
 * <p><b>The host's own limits leave by this type's abort.</b> A whole number is held by a host that has
 * a largest one, and a number past it is one no value here is made of — so no method of this type
 * answers with an exception of the host's arithmetic, which says nothing about a Rational to whoever
 * reads it (ADR-0112). The translation is here and not at the operators, because it is here that the
 * host is reached: {@code List.sum} over these asks this type for a sum directly, and an operator that
 * caught what it never called would have left the fold answering the other way.
 *
 * <p><b>Which bound each operation rests on.</b> Three bounds stand behind everything here, and they are
 * not the same kind of thing. The exponent's width, a decimal's scale and how large a part this stores
 * ({@link #STORED_BITS}) are <i>this representation's</i>: a value past them has none here, so an operation
 * reaching one refuses a value rather than a step — and refuses the value, which is why the last of them is
 * read off what is stored and not off the numbers a caller wrote. The platform's own largest whole number
 * is the <i>room this runs in</i>, and it bounds what is formed on the way to a value rather than which
 * values there are; the bound above is set so that nothing a comparison forms reaches it. A bracket's width
 * is neither: it is an <i>instrument</i>, and an instrument too coarse for a question is a reason to take a
 * finer one and never a reason to refuse.
 *
 * <p>So: the product, the quotient and both narrowings build only the answer's own parts. The order and
 * the rounding take a bracket first, because one settles nearly every question for nothing; where it does
 * not, the two values stand close, and then the powers between them are written down and the question is
 * answered exactly — one fraction against another by the walk a common measure takes, which forms no
 * product of two stored numbers and asks for no width. That is not conditioned on the powers happening to
 * cancel: two fractions can stand closer together than any width settled on before they arrive, whatever
 * powers stand between them, and a width is only the instrument for the pairs brought close by exponents
 * too large to be worth writing down — whose closeness is bounded by how well whole numbers approximate the
 * log. Which of the two ways a pair is answered is a question of cost alone, both being exact.
 *
 * <p>The sum is the one operation that forms a number larger than its answer, and it is the one whose
 * formed number is not a route to the answer but the answer's own definition: an exact sum is the sum of
 * two numerators over a common denominator, and what cancels in it is visible only once those terms are
 * there. So a pair of stored fractions near the host's own end has no sum here, and that is said as a
 * limit of the operation rather than dressed up as a limit of the machine.
 */
public record Rational(BigInteger numerator, BigInteger denominator, long twos, long fives)
        implements Comparable<Rational> {

    /** Declared before the two values below, which are built by a constructor that reads it. */
    private static final BigInteger FIVE = BigInteger.valueOf(5);

    /** The denominator of half of one, which is what a remainder is compared against to say which side
     *  of half way between two whole numbers a value stands. */
    private static final BigInteger HALVES = BigInteger.valueOf(2);

    public static final Rational ZERO = new Rational(BigInteger.ZERO, BigInteger.ONE, 0, 0);
    public static final Rational ONE = new Rational(BigInteger.ONE, BigInteger.ONE, 0, 0);

    /**
     * How many bits a power of five is first bracketed to when a comparison asks for one.
     *
     * <p>A starting point and not a limit: a bracket too wide to separate the pair it was taken for is
     * taken again wider ({@link WorkingWidth}). Wide enough that the second turn is not reached by any
     * pair a comparison is likely to be asked about — the exponents would have to put the two values
     * within this many bits of one another — and small enough that the first turn is a few dozen
     * multiplications of numbers this size.
     */
    private static final int BRACKET_BITS = 128;

    /**
     * How many times over what a pair already takes up a cheap exact writing of it may form.
     *
     * <p>A cost policy and nothing else — every value it turns away is answered by the reading below it.
     * Over the two and a third bits a factor of five takes, so that a pair whose exponents nearly cancel is
     * written out rather than refined, and small enough that a pair brought close by exponents too large to
     * write down is refined rather than written.
     */
    private static final int A_FEW_TIMES = 4;

    /** More bits than a factor of five takes, which is over two and a third of them. Counted over the truth
     *  so that the count of what a writing would cost is over it too. */
    private static final int MORE_BITS_THAN_A_FIVE_TAKES = 3;

    /**
     * How many bits a stored numerator or denominator holds. A value whose parts want more of them has no
     * representation here and aborts, as one whose exponent wants more than sixty-four bits does.
     *
     * <p><b>Why this type bounds its parts at all,</b> when the platform's own largest whole number is far
     * larger. Because the order has to be answered for every pair this type holds, and how much working
     * room that takes is set by the parts: telling two values apart takes as many bits as they agree over.
     * Left to the platform's own end, a pair of parts near it would want a bracket of several times that
     * end — and a bracket is one whole number, which the platform counts the bits of in a thirty-two-bit
     * count. So the width the question needed would have been past what the instrument can be, and that is
     * not the platform running out of room: more of it would not help, and the same pair would go
     * unanswered on any machine. It would be this implementation's own limit wearing the platform's name.
     *
     * <p>A bound on the parts is the other way to close that, and it is the one the language already has a
     * shape for: a representation may bound what it holds, and a value past the bound aborts (spec
     * §stdlib-rational). It is a bound on the value, in one place, said out loud — as against a limit on
     * which pairs can be ordered, which is a bound on the operation and one the order may not carry.
     *
     * <p><b>What the number has to keep true.</b> Two things, and whoever changes it has to keep both:
     *
     * <pre>{@code
     * the width a pair of parts of S bits can want    W ≤ k · S + C
     * the largest number a bracket of width W forms   2 · W + C' ≤ what the platform builds
     * }</pre>
     *
     * <p>The second is a fact about the code below: a bracket of some width squares its ends and shifts a
     * numerator up by the width, so what it forms is about twice the width and nothing here is worse than
     * that. The first is where the reasoning is. Two values the starting bracket leaves open are brought
     * close either by their exponents or by their parts. By their exponents alone the closest they come is a
     * power of two against a power of five, and whole numbers of sixty-four bits put those logarithms some
     * sixty bits apart — which the starting width settles, so this is not the case that sets {@code k}.
     * Closer than that is the parts' doing, and a fraction of so many bits closes on what it approximates
     * to about twice that many, whence {@code k} of about four over the two parts.
     *
     * <p>That last step is an estimate and is said to be one. "About twice that many" is how well a
     * fraction of a size <i>can</i> approximate, not a floor on how close any particular target lies: a
     * partial quotient out of the ordinary in the right place puts a closer one there, and the exponents
     * offer many targets to look through. So the number carries a factor of two over the estimate — a
     * sixteenth where an eighth is what the two lines above ask for — and the estimate is only ever load
     * bearing for how far the refinement climbs. Where it is wrong the outcome is a shortage reported as
     * one, never a wrong answer: a bracket holds the value it was taken for however wide it was taken, so
     * no reading here can be made to answer by having too little room, only to stop.
     *
     * <p>What it costs is values no operator here builds. An {@code Int} is sixty-four bits and a
     * {@code Decimal}'s unscaled value is a whole number the platform holds; what reaches this is a sum
     * across distant exponents, which builds the difference between them — so a fold of values whose scales
     * are spread over a hundred million places aborts here, where before it aborted at the platform's end.
     */
    static final int STORED_BITS = Integer.MAX_VALUE / 16;


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
            throw new IllegalArgumentException(
                    "a rational has no zero denominator: " + spelled(numerator) + "/0");
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
                twos = added(twos, inNumerator);
            }
            int inDenominator = denominator.getLowestSetBit();
            if (inDenominator > 0) {
                denominator = denominator.shiftRight(inDenominator);
                twos = added(twos, -inDenominator);
            }
            // One five at a time, which costs a division per trailing zero of the number it is taking
            // them off. That is bounded by the digits the number already has, so nothing here is
            // amplified by the exponents this type carries — a power of ten held as a scale never
            // reaches this loop at all.
            while (true) {
                BigInteger[] divided = numerator.divideAndRemainder(FIVE);
                if (divided[1].signum() != 0) {
                    break;
                }
                numerator = divided[0];
                fives = added(fives, 1);
            }
            while (true) {
                BigInteger[] divided = denominator.divideAndRemainder(FIVE);
                if (divided[1].signum() != 0) {
                    break;
                }
                denominator = divided[0];
                fives = added(fives, -1);
            }
        }
        // Last, and of what is stored rather than of what arrived. The bound is on the value, and the parts
        // a caller wrote are one spelling of it: a numerator of a hundred and thirty-four million bits that
        // is a power of two is the number one here, with the rest of it in an exponent. Asked of the spelling
        // instead, this turned away values it holds — and turned them away for the size of a form it had
        // chosen itself, which is the one reason nothing here may refuse for.
        heldByTheRepresentation(numerator);
        heldByTheRepresentation(denominator);
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
        return new Rational(denominator, numerator, negated(twos), negated(fives));
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
        try {
            return new Rational(
                    numerator.divide(acrossOne).multiply(other.numerator.divide(acrossTwo)),
                    denominator.divide(acrossTwo).multiply(other.denominator.divide(acrossOne)),
                    added(twos, other.twos),
                    added(fives, other.fives));
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    /**
     * The quotient. The exponents subtract and are never built, and the cross factors come off before
     * the multiplication, as they do for the product.
     *
     * <p>Not one over the divisor, multiplied in. A reciprocal's exponents are the divisor's negated,
     * and the least sixty-four-bit number has no positive counterpart — so a quotient reached that way
     * refused pairs whose own exponents are the difference of two held ones, with {@code r / r} among
     * them. The difference is what the answer's exponents are, so it is what is computed.
     */
    public Rational dividedBy(Rational other) {
        if (other.isZero()) {
            throw new IllegalArgumentException("nought divides nothing");
        }
        if (isZero()) {
            return ZERO;
        }
        BigInteger acrossOne = numerator.gcd(other.numerator);
        BigInteger acrossTwo = denominator.gcd(other.denominator);
        try {
            return new Rational(
                    numerator.divide(acrossOne).multiply(other.denominator.divide(acrossTwo)),
                    denominator.divide(acrossTwo).multiply(other.numerator.divide(acrossOne)),
                    lessened(twos, other.twos),
                    lessened(fives, other.fives));
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
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
        long commonTwos = Math.min(twos, other.twos);
        long commonFives = Math.min(fives, other.fives);
        try {
            BigInteger here = numerator.multiply(
                    raised(lessened(twos, commonTwos), lessened(fives, commonFives)));
            BigInteger there = other.numerator.multiply(
                    raised(lessened(other.twos, commonTwos), lessened(other.fives, commonFives)));
            BigInteger shared = denominator.gcd(other.denominator);
            BigInteger overThis = denominator.divide(shared);
            Summed sum = summed(
                    here.multiply(other.denominator.divide(shared)), there.multiply(overThis));
            return new Rational(sum.whole(), overThis.multiply(other.denominator),
                    added(commonTwos, sum.twos()), commonFives);
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    public Rational minus(Rational other) {
        return plus(other.negated());
    }

    /** A sum, and the factors of two taken off it while it was formed. */
    record Summed(BigInteger whole, int twos) {}

    /**
     * The sum of two whole numbers, with its factors of two taken off as it is formed rather than after.
     *
     * <p>The host holds a largest whole number, and two numbers it holds can have a sum wanting one bit
     * more — while the Rational that sum stands for holds that bit as an exponent and is an ordinary
     * value. So where the sum is even what is formed is its odd part, and the factors of two go where
     * every other factor of two in this type goes.
     *
     * <p>Only the factors of two, and so only the sums whose extra bit is one of those. A sum of two odd
     * numbers is even and is the shape a carry takes when neither side can give a bit back; a sum with one
     * side odd is odd, and is as large as it is going to be. What that leaves is a sum of a size the host
     * holds or a sum that has no representation here at all, except where the extra bit would have come
     * off as a five instead — which is not taken off, five having no halving that leaves both sides where
     * they are.
     *
     * <p>Neither side has to be made larger to halve their sum. Where both are even, both come down;
     * where both are odd, {@code (a + b) / 2} is {@code a/2 + b/2 + 1}, which holds for two negatives as
     * well, the halving being the one that rounds down on both. Where one is odd and the other even the
     * sum is odd, and then it is its own odd part and as large as it is going to be.
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
     * Where this stands against {@code other} by exact mathematical value.
     *
     * <p>Answered for every pair this type holds, and answered without building a power for all but the
     * pairs where building one is the cheaper way. What the two values are made of beyond their stored
     * fractions is a power of two, which is a count of bits, and a power of five, which is bracketed
     * between two whole numbers of a working width by squaring — so the work is the bits of an exponent
     * rather than its size, and a comparison of a millionth of a millionth against one costs a few dozen
     * multiplications of numbers that width.
     *
     * <p>Where the bracket is too wide to separate the pair, the readings under {@link #compareMagnitude}
     * take over: the powers are written down where that costs about what the pair already does, and where
     * it does not the bracket is taken again wider until the two come apart. The rising ends, because two
     * values with one canonical representation each are equal exactly where those representations are, and
     * unequal ones stand a fixed distance apart for a bracket to get inside of. Which is the whole of why
     * this rests on brackets rather than on the numbers: the exponents run to sixty-four bits, so the pairs
     * whose logs sit closest together are also the ones whose digits no machine holds.
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
        // Nothing here is translated. Every number a comparison forms is either one of the working width,
        // which is what bracketing each side whole rather than cross-multiplying the two fractions buys,
        // or one asked of the host by whoever forms it and answered for where it does not fit.
        int byMagnitude = compareMagnitude(other);
        return signum() > 0 ? byMagnitude : -byMagnitude;
    }

    /**
     * Where {@code |this|} stands against {@code |other|}, both being non-zero.
     *
     * <p>Each side is bracketed whole — its fraction as much as its powers — so nothing larger than the
     * working width is ever multiplied. Cross-multiplying the two fractions instead put one half of each
     * value through a bracket and the other half through a product of two stored numbers, and a product
     * of two numbers the host holds is not always one it holds. The answer is one of three and always
     * has a representation, so a comparison that asked for that product refused pairs over a step.
     *
     * <p>The two magnitudes are unequal, which is what makes the refinement end. The caller has that:
     * one canonical representation per value means two values of one magnitude and one sign are the same
     * record, and the comparison above answered those before reaching here.
     *
     * <p><b>Four readings, and only the last one always answers.</b> The three above it are there because
     * they are cheap, and each is allowed to decline: a bracket of the starting width settles nearly every
     * pair for a few dozen multiplications of small numbers; writing both values out as one fraction each
     * settles a pair whose powers are worth writing down; and the same writing with the exponents'
     * difference on one side settles a pair whose huge exponents cancel. What is left over goes to the
     * refinement, which asks for no width in advance and so has nothing to decline for.
     */
    private int compareMagnitude(Rational other) {
        return magnitudeWithAWritingWorth(
                other, bitsAWritingIsWorth(storedBits() + other.storedBits()));
    }

    /**
     * The same, with what a writing may cost stated rather than worked out.
     *
     * <p>Apart from the comparison so that the readings can be asked for as a sequence — a pair the bracket
     * leaves open, a writing that declines, and the refinement answering — which is what a fixture cannot
     * otherwise put a question to. The pairs that reach the refinement in earnest are the ones whose powers
     * no machine writes down, and a value carrying one of those is not something a test builds. Told that no
     * writing is worth anything, the readings take the same route for a pair a test can check the answer of.
     */
    int magnitudeWithAWritingWorth(Rational other, long bitsAWritingMayForm) {
        Integer quickly = magnitudeFromBrackets(other, BRACKET_BITS);
        if (quickly != null) {
            return quickly;
        }
        // The bracket did not separate them, so they stand close. Then the pair is written out as two
        // fractions and compared exactly, at whatever closeness it happens to have.
        Integer exactly = magnitudeWrittenOut(other, bitsAWritingMayForm);
        if (exactly != null) {
            return exactly;
        }
        // And asked the other way about, which is a different pair of fractions to write out and so a
        // different question about cost. Where one side's powers cancel the other's, only one of the two
        // writings is worth taking — and which of them that is has nothing to do with which value was asked
        // about, so an order that took one writing and stopped read one pair two ways.
        Integer theOtherWayAbout = other.magnitudeWrittenOut(this, bitsAWritingMayForm);
        if (theOtherWayAbout != null) {
            return -theOtherWayAbout;
        }
        return magnitudeByRefining(other);
    }

    /** How many bits the parts a value stores take up, which is what holding it costs. */
    private long storedBits() {
        return (long) numerator.abs().bitLength() + denominator.bitLength();
    }

    /**
     * How large a whole number a writing may form before the refinement is the cheaper way to the answer,
     * for values whose stored parts take up this many bits.
     *
     * <p>A cost and nothing else. Once the refinement answers every pair, what the readings above it are for
     * is being cheap, so what they must decide is not whether the host could hold the number but whether the
     * number is worth forming — and the two questions have different answers over a range where the second
     * is the one that matters. A power of five of some hundreds of millions is a few hundred megabytes and
     * minutes of work; the host holds it, and the refinement would have settled the same pair at a few
     * thousand bits. Asked the first question, the reading spent that; asked this one, it declines and costs
     * nothing.
     *
     * <p>A multiple of what the values already take up, because that is what the refinement costs. Telling
     * two values apart takes as many bits as they agree over, and two values whose stored fractions are of
     * some size cannot agree over much more than that size unless their exponents very nearly cancel — in
     * which case what the writing forms is of that size too. So a writing much larger than the stored parts
     * is one the refinement beats, and a writing near them is one it does not.
     *
     * <p>Declining where the writing would have done is free. It sends the pair to a reading that answers,
     * which is why the two questions could be told apart at all: while the writing was the last word, a
     * reading that turned away what it could have written left the order unanswered, so its test had to lean
     * the other way — towards attempting anything the host might hold.
     */
    private static long bitsAWritingIsWorth(long stored) {
        return A_FEW_TIMES * stored + BRACKET_BITS;
    }

    /**
     * Where {@code |this|} stands against {@code |other|}, from brackets taken again wider until they
     * come apart, both magnitudes being unequal and above nought.
     *
     * <p>This is the reading the promise about the order is made of, and the three cheaper ones above it
     * are what keep it from being reached. It holds nothing back: a bracket holds the value it was taken
     * for by how it was built, so a pair the brackets separate is separated exactly, and two unequal
     * magnitudes stand some distance apart for a bracket to get inside of. So the width that answers is
     * the one the pair has, and the only way this does not answer is the host running out of room to hold
     * the next width — which is the run failing and not a pair declined.
     *
     * <p>Apart from {@link #compareMagnitude} so that a test can ask this rung the pairs the ones above it
     * would have answered, and see it answer them. Reached only through them, it would be the rung no
     * fixture can put a question to: the pairs that reach it are the ones whose fractions the host has no
     * room to write, which is a fixture no machine builds.
     */
    int magnitudeByRefining(Rational other) {
        return asWideAsItTakes(
                width -> magnitudeFromBrackets(other, width),
                () -> "tell " + this + " from " + other);
    }

    /** A question a bracket of some width either settles or leaves open. */
    interface ReadFromABracket<T> {
        @Nullable T atAWidthOf(int bits);
    }

    /**
     * The first answer a reading gives as the width rises, and the run's failure where no width this run
     * holds gives one.
     *
     * <p>One mechanism for the order and for the rounding, which ask the same thing of a bracket: both are
     * a question with finitely many answers whose subject is an exact value, so both are settled by any
     * bracket tight enough and by no width known before the value arrives. Here rather than in either, so
     * that how fast a width rises is not a decision sitting in the middle of what an order means, and so
     * that the next reading wanting a bracket gets the refinement rather than a third copy of it.
     *
     * <p>The run's shortage at one width is caught, and no other thing is. A width the host has no room for
     * says nothing about the widths below it, so the reading is not finished — what is finished is the
     * rising, and what follows is the search for the widest width there is room for. An abort of this
     * language, from a reading that found the answer itself has no representation, is a different thing and
     * passes through untouched. So does an error of the host's own, running out of memory being the run
     * failing in the way every run does and not something to be worked around.
     *
     * <p>Reachable to a test with a reading of its own, because the two widths this is about — the one the
     * question needs and the one the host will not hold — are hundreds of megabytes apart for any reading
     * here, and a fixture that put them where a test can see them would not be this mechanism.
     */
    static <T> T asWideAsItTakes(
            ReadFromABracket<T> reading, Supplier<String> theQuestion) {
        WidthsToTry widths = WidthsToTry.aboveAWidthOf(BRACKET_BITS);
        while (widths.thereIsOneToTry()) {
            int width = widths.next();
            T decided;
            try {
                decided = reading.atAWidthOf(width);
            } catch (OutOfRoom _) {
                widths = widths.wasTooWide(width);
                continue;
            }
            if (decided != null) {
                return decided;
            }
            widths = widths.wasNotWideEnough(width);
        }
        throw new OutOfRoom("this run has no room to " + theQuestion.get());
    }

    /**
     * The widths a reading is taken at: which to try next, given the widest one known to be held and the
     * narrowest one known to be past what the host holds.
     *
     * <p>Its own type because two searches are going on here and the reading is the subject of neither. One
     * is for the precision the question needs, which rises; the other is for where the host's room gives
     * out, which is found only by asking. Written as a rising alone, the second was assumed to be the first
     * width that failed — so a width that asked for too much ended the whole thing, while a narrower one
     * the host did hold and that would have settled the question went untried. A rate of rise is a decision
     * about cost; treating the first failure as the frontier was a decision about the answer, made by the
     * same arithmetic.
     *
     * <p>So the rise stops at the first failure and the search turns inward: between a width that was held
     * and one that was not, it tries the middle, and either side of that middle tells it which half to keep.
     * That ends, the two closing on one another, and it ends having tried a width the host holds and within
     * a bit of the widest there is. Only then is the room genuinely out.
     *
     * <p>Half again each turn while it rises. The number of turns is proportional to the log of how closely
     * the pair stands either way, and the whole costs what its last turn costs either way — so what the
     * gentler rise buys is asking the host for less past the width that would have done. Never by fewer than
     * a few dozen bits, so that the rise is not slow while the width is small. The widest width the host
     * counts is tried rather than stepped over, a rise being no reason to skip it.
     */
    private record WidthsToTry(int held, int past) {

        private static final int A_FEW_DOZEN_BITS = 64;

        /** No width is known to be past what the host holds until one has failed, and nought is no width. */
        private static final int NONE_HAS_FAILED = 0;

        static WidthsToTry aboveAWidthOf(int held) {
            return new WidthsToTry(held, NONE_HAS_FAILED);
        }

        boolean thereIsOneToTry() {
            return past == NONE_HAS_FAILED ? held < Integer.MAX_VALUE : past - held > 1;
        }

        int next() {
            if (past == NONE_HAS_FAILED) {
                return (int) Math.min(
                        held + Math.max(A_FEW_DOZEN_BITS, held / 2L), Integer.MAX_VALUE);
            }
            return held + (past - held) / 2;
        }

        WidthsToTry wasNotWideEnough(int width) {
            return new WidthsToTry(width, past);
        }

        WidthsToTry wasTooWide(int width) {
            return new WidthsToTry(held, width);
        }
    }

    /**
     * Where {@code |this|} stands against {@code |other|} by writing both out as one fraction each, and
     * null where what that takes altogether is not worth forming.
     *
     * <p>Each value is written out at its own exponents first, which is the writing that does not depend on
     * which of the two was asked about. Where that is not worth it, the difference of the two exponents is
     * put on this side instead and the other side is left as it stands — two values of huge but equal
     * exponents cancel that way and are written out where their own forms would have cost too much.
     *
     * <p>A writing is what its numbers come to together, because they are all held at once and it is what
     * the reading costs that is being weighed. Weighed one at a time against the same budget, a writing of
     * four numbers each just inside it cost four times what the budget said.
     */
    @Nullable Integer magnitudeWrittenOut(Rational other, long within) {
        BigInteger @Nullable [] eachAtItsOwn = allWrittenOut(within,
                new ToWriteOut(numerator.abs(), BigInteger.valueOf(twos), BigInteger.valueOf(fives)),
                new ToWriteOut(denominator,
                        BigInteger.valueOf(twos).negate(), BigInteger.valueOf(fives).negate()),
                new ToWriteOut(other.numerator.abs(),
                        BigInteger.valueOf(other.twos), BigInteger.valueOf(other.fives)),
                new ToWriteOut(other.denominator,
                        BigInteger.valueOf(other.twos).negate(), BigInteger.valueOf(other.fives).negate()));
        if (eachAtItsOwn != null) {
            return comparedAsFractions(
                    eachAtItsOwn[0], eachAtItsOwn[1], eachAtItsOwn[2], eachAtItsOwn[3]);
        }
        BigInteger byTwos = apart(twos, other.twos);
        BigInteger byFives = apart(fives, other.fives);
        BigInteger @Nullable [] theDifferenceOnThisSide = allWrittenOut(within,
                new ToWriteOut(numerator.abs(), byTwos, byFives),
                new ToWriteOut(denominator, byTwos.negate(), byFives.negate()));
        return theDifferenceOnThisSide == null ? null
                : comparedAsFractions(theDifferenceOnThisSide[0], theDifferenceOnThisSide[1],
                        other.numerator.abs(), other.denominator);
    }

    /** A whole number to be written out with powers in it: what the powers multiply, and the powers. A
     *  negative one of them belongs to the other side of the fraction and counts for nothing here. */
    private record ToWriteOut(BigInteger whole, BigInteger twos, BigInteger fives) {

        /** How many bits writing it out takes, counted over the truth so that a writing is turned away
         *  rather than attempted where the count is the wrong side of the budget. */
        BigInteger bits() {
            return BigInteger.valueOf(whole.bitLength())
                    .add(twos.max(BigInteger.ZERO))
                    .add(fives.max(BigInteger.ZERO)
                            .multiply(BigInteger.valueOf(MORE_BITS_THAN_A_FIVE_TAKES)));
        }

        @Nullable BigInteger written() {
            return writtenOut(whole, twos, fives);
        }
    }

    /** All of them written out, or null where what they come to together is past {@code within} bits or
     *  where the host turns one of them down after all. */
    private static BigInteger @Nullable [] allWrittenOut(long within, ToWriteOut... these) {
        BigInteger bits = BigInteger.ZERO;
        for (ToWriteOut one : these) {
            bits = bits.add(one.bits());
        }
        if (bits.compareTo(BigInteger.valueOf(within)) > 0) {
            return null;
        }
        BigInteger[] written = new BigInteger[these.length];
        for (int at = 0; at < these.length; at++) {
            BigInteger one = these[at].written();
            if (one == null) {
                return null;
            }
            written[at] = one;
        }
        return written;
    }

    /** How far one exponent stands from another, held wider than an exponent is — the difference of two
     *  of them is not bounded by what one of them holds. */
    private static BigInteger apart(long exponent, long from) {
        return BigInteger.valueOf(exponent).subtract(BigInteger.valueOf(from));
    }

    /**
     * A whole number written out with those powers in it, or null where the host turns it down.
     *
     * <p>What it would cost is counted before this is reached, by whoever is weighing the whole writing, and
     * counted over the truth rather than under it — a factor of five taken as three bits when it is nearer
     * two and a third. So a writing that would have fitted its budget is sometimes turned away, and that is
     * the side to be wrong on: a writing turned away costs nothing and the pair is answered by the
     * refinement, while a writing attempted at hundreds of megabytes costs that whether or not it ends in a
     * number.
     *
     * <p>Which is the opposite of how this had to lean while the writing was the last word. Then a count
     * that turned away what the host would have held left the order unanswered, so the count was kept under
     * the truth and everything else was attempted and let stand or not by whoever held it — and a power of
     * five of some hundreds of millions passed that test, took minutes, and ended in nothing. The host's own
     * refusal is still caught here, a budget being a cost and not a promise about what fits.
     */
    private static @Nullable BigInteger writtenOut(
            BigInteger whole, BigInteger twos, BigInteger fives) {
        try {
            return builtFrom(whole, twos.max(BigInteger.ZERO), fives.max(BigInteger.ZERO));
        } catch (ConstraintViolation _) {
            return null;
        } catch (ArithmeticException _) {
            return null;
        }
    }

    /**
     * Where {@code |this|} stands against {@code |other|} as far as brackets of {@code width} bits
     * settle it, and null where the two brackets overlap and a tighter pair is what answers.
     *
     * <p>Separate from the comparison above so that both of its answers are asked for directly. A
     * width that always overlapped would leave the comparison correct and looping, and a width that
     * always decided would leave the refinement above it unreached — a comparison is the reader that
     * cannot tell either from a bracket that works.
     *
     * <p>Everything this forms is an instrument, the two brackets and the numbers they are held against
     * alike, so a width the host has no room for anywhere in here is the run's shortage. The translation is
     * around the whole reading rather than around the step that happened to reach the host first: which step
     * that is depends on the width and on the values, and a reading whose outcome is settled, open, or the
     * run's has no fourth outcome to leave by.
     */
    @Nullable Integer magnitudeFromBrackets(Rational other, int width) {
        try {
            Bracketed here = bracketedMagnitude(width);
            Bracketed there = other.bracketedMagnitude(width);
            if (compareShifted(here.low(), here.shift(), there.high(), there.shift()) > 0) {
                return 1;
            }
            if (compareShifted(here.high(), here.shift(), there.low(), there.shift()) < 0) {
                return -1;
            }
            return null;
        } catch (ArithmeticException e) {
            throw new OutOfRoom(
                    "this run has no room to compare at a width of " + width + " bits: " + e.getMessage());
        }
    }

    /**
     * This value's magnitude, held between two whole numbers of {@code width} bits.
     *
     * <p>The fraction is bracketed by one division rather than kept whole, which is what keeps every
     * number here to the working width: a numerator shifted to meet a denominator is the size of the
     * larger of the two, where a numerator multiplied by another value's denominator is the size of
     * both together — and two numbers the host holds can have a product it does not.
     */
    private Bracketed bracketedMagnitude(int width) {
        return bracketed(BigInteger.valueOf(twos), BigInteger.valueOf(fives), width);
    }

    /**
     * The magnitude of this value with {@code byTwos} and {@code byFives} standing in for its own
     * exponents, held between two whole numbers of about {@code width} bits.
     *
     * <p>Taken at other exponents by the narrowing, which asks about this value times a power of ten and
     * so about exponents a scale has been added to. The rest is the same reading, and is one reading
     * rather than two because the shape it has to avoid is the same in both: a stored fraction multiplied
     * outside the bracket is a number as large as the fraction, whatever the bracket is kept to.
     *
     * <p>A width the host has no room for leaves as the run's shortage and not as a value refused, and
     * leaves that way here, where the host is reached. A bracket is an instrument: the value it was taken
     * for has a representation, the answer it was taken towards has one, and what was not to be had is a
     * number this type never stores. So the reading above is left with two outcomes rather than three —
     * settled, or not settled at this width — and a caller refining it is spared having to tell a shortage
     * of room from an abort about the answer, which is a distinction no {@code catch} of the host's
     * arithmetic can make.
     */
    private Bracketed bracketed(BigInteger byTwos, BigInteger byFives, int width) {
        try {
            Bracketed of = quotientBracketed(numerator.abs(), denominator, width);
            if (byFives.signum() != 0) {
                Bracketed five = fiveTo(byFives.abs(), width);
                of = of.times(byFives.signum() > 0 ? five : five.reciprocal(width), width);
            }
            return of.shiftedBy(byTwos);
        } catch (ArithmeticException e) {
            throw new OutOfRoom(
                    "this run has no room for a bracket of " + width + " bits: " + e.getMessage());
        }
    }

    /**
     * {@code x / y} held between two whole numbers of about {@code width} bits, {@code x} being at least
     * nought and {@code y} above it.
     *
     * <p>Both sides are cut to the width first and what was cut off becomes part of the shift, so nothing
     * here is the size of either of them. A quotient's leading bits are decided by the leading bits of
     * the two numbers, and reaching them by moving the numerator up instead asks for room above it that a
     * stored fraction at the end of what the host holds does not have — a distance that then does not fit
     * in the count a shift is given, and a shift of a negative count is a shift the other way. What comes
     * of that is not a refusal but a bracket with the value outside it, which is an order answered wrongly.
     */
    private static Bracketed quotientBracketed(BigInteger x, BigInteger y, int width) {
        Bracketed over = leadingBits(x, width);
        Bracketed under = leadingBits(y, width);
        return new Bracketed(
                over.low().shiftLeft(width).divide(under.high()),
                over.high().shiftLeft(width).divide(under.low()).add(BigInteger.ONE),
                over.shift().subtract(under.shift()).subtract(BigInteger.valueOf(width)));
    }

    /**
     * Where {@code a/b} stands against {@code c/d}, all four being above nought.
     *
     * <p>Exact, and never a product of any two of them. The whole parts of the two are compared, and where
     * those agree what is left over is compared the other way about — the greater remainder over the same
     * kind of thing makes the lesser fraction. That is the walk a common measure takes, so it ends in as
     * many steps as one does, and every number in it is a remainder of numbers already there.
     *
     * <p>Cross-multiplying instead asks for a number as large as two of them together, which refuses a
     * pair the host holds both sides of. A bracket asks for a width instead, and two fractions of one size
     * can stand a part in that size apart — closer than any width settled on ahead of the pair. This asks
     * for neither.
     */
    private static int comparedAsFractions(BigInteger a, BigInteger b, BigInteger c, BigInteger d) {
        BigInteger up = a;
        BigInteger over = b;
        BigInteger against = c;
        BigInteger by = d;
        boolean theOtherWayAbout = false;
        while (true) {
            BigInteger[] here = up.divideAndRemainder(over);
            BigInteger[] there = against.divideAndRemainder(by);
            int byWhole = here[0].compareTo(there[0]);
            if (byWhole != 0) {
                return theOtherWayAbout ? -byWhole : byWhole;
            }
            boolean hereEnds = here[1].signum() == 0;
            boolean thereEnds = there[1].signum() == 0;
            if (hereEnds || thereEnds) {
                int ended = hereEnds ? (thereEnds ? 0 : -1) : 1;
                return theOtherWayAbout ? -ended : ended;
            }
            up = over;
            over = here[1];
            against = by;
            by = there[1];
            theOtherWayAbout = !theOtherWayAbout;
        }
    }

    /** A whole number's leading bits: what was cut off is the shift, and the number stands between the
     *  bits that are left and one more of them. */
    private static Bracketed leadingBits(BigInteger whole, int width) {
        int over = whole.bitLength() - width;
        if (over <= 0) {
            return Bracketed.exactly(whole);
        }
        BigInteger kept = whole.shiftRight(over);
        return new Bracketed(kept, kept.add(BigInteger.ONE), BigInteger.valueOf(over));
    }

    /**
     * Where {@code x × 2^a} stands against {@code y × 2^b}, both whole numbers being above nought.
     *
     * <p>Each side stands between its own count of bits and one more, so a gap of over one bit is read
     * off those counts and neither side is shifted — which is what keeps a shift no machine holds out
     * of this. Within a bit of one another, the two shifts are apart by no more than the bits the two
     * numbers hold, and the lesser side is lifted to meet the other.
     */
    private static int compareShifted(BigInteger x, BigInteger a, BigInteger y, BigInteger b) {
        BigInteger apart = a.add(BigInteger.valueOf(x.bitLength()))
                .subtract(b.add(BigInteger.valueOf(y.bitLength())));
        if (apart.compareTo(BigInteger.ONE) > 0) {
            return 1;
        }
        if (apart.negate().compareTo(BigInteger.ONE) > 0) {
            return -1;
        }
        BigInteger lift = a.subtract(b);
        return lift.signum() >= 0
                ? x.shiftLeft(lift.intValueExact()).compareTo(y)
                : x.compareTo(y.shiftLeft(lift.negate().intValueExact()));
    }

    /**
     * {@code 5^exponent} bracketed to {@code width} bits, the exponent being at least nought.
     *
     * <p>Squared up from the exponent's bits, so the work is how many bits the exponent has and not
     * how large it is: a power of five whose digits no machine holds is bracketed here in as many
     * multiplications of numbers this wide as the exponent has bits.
     */
    private static Bracketed fiveTo(BigInteger exponent, int width) {
        Bracketed of = Bracketed.exactly(BigInteger.ONE);
        for (int bit = exponent.bitLength() - 1; bit >= 0; bit--) {
            of = of.squared(width);
            if (exponent.testBit(bit)) {
                of = of.times(FIVE).keptTo(width);
            }
        }
        return of;
    }

    /**
     * A number held between two whole numbers a count of bits short of it: the number is at least
     * {@code low × 2^shift} and at most {@code high × 2^shift}.
     *
     * <p>Every step keeps the number between the two by rounding each end away from it, so what a
     * bracket says is true by how it was built rather than by an error anyone has to have got right.
     * What a width buys is how tight the bracket is, never whether it holds.
     */
    private record Bracketed(BigInteger low, BigInteger high, BigInteger shift) {

        static Bracketed exactly(BigInteger whole) {
            return new Bracketed(whole, whole, BigInteger.ZERO);
        }

        Bracketed times(BigInteger by) {
            return new Bracketed(low.multiply(by), high.multiply(by), shift);
        }

        /** The product of two brackets, which holds the product of any two numbers they hold — both
         *  standing above nought, so the ends multiply in the order they are in. */
        Bracketed times(Bracketed other, int width) {
            return new Bracketed(low.multiply(other.low), high.multiply(other.high),
                    shift.add(other.shift)).keptTo(width);
        }

        /**
         * One over this, bracketed to {@code width} bits.
         *
         * <p>The ends change places, the lower of the two coming from the upper of these. Nothing here is
         * larger than the width either: a one shifted up to meet an end and divided by it answers the
         * bits asked for, and the shift is the end's own size rather than anything's product.
         *
         * <p>The distance to shift by is a count of bits and is added as one. Added as an {@code int} — the
         * width and a bit length both being that — it wraps where the two together run past what one
         * counts, and a shift of a negative count is a shift the other way, so what came of it was a
         * bracket with the value outside it rather than a refusal. That is an order answered wrongly, which
         * is the one outcome no instrument may have.
         */
        Bracketed reciprocal(int width) {
            int by = bitsTheHostAddresses((long) width + high.bitLength());
            BigInteger over = BigInteger.ONE.shiftLeft(by);
            return new Bracketed(
                    over.divide(high), over.divide(low).add(BigInteger.ONE),
                    BigInteger.valueOf(-by).subtract(shift));
        }

        Bracketed shiftedBy(BigInteger bits) {
            return new Bracketed(low, high, shift.add(bits));
        }

        Bracketed squared(int width) {
            return new Bracketed(low.multiply(low), high.multiply(high), shift.add(shift))
                    .keptTo(width);
        }

        /** The same number, held between two numbers of no more than {@code width} bits. The lower end
         *  falls to where the shift leaves it and the upper end rises to the next one up, so the number
         *  stays inside. */
        Bracketed keptTo(int width) {
            int over = high.bitLength() - width;
            if (over <= 0) {
                return this;
            }
            BigInteger down = low.shiftRight(over);
            BigInteger up = high.shiftRight(over);
            if (up.shiftLeft(over).compareTo(high) < 0) {
                up = up.add(BigInteger.ONE);
            }
            return new Bracketed(down, up, shift.add(BigInteger.valueOf(over)));
        }
    }

    /** {@code 2^twos × 5^fives}, both exponents being non-negative. */
    private static BigInteger raised(long twos, long fives) {
        int byTwos = buildable(twos);
        int byFives = buildable(fives);
        heldByTheHost(byTwos + 2L * byFives);
        BigInteger of = BigInteger.ONE.shiftLeft(byTwos);
        return byFives == 0 ? of : of.multiply(FIVE.pow(byFives));
    }

    /**
     * That a whole number of this many bits is one the host holds, asked before it is built.
     *
     * <p>A {@code BigInteger} is addressed by a count of bits, so there is a size past which the host has
     * none — and a whole number the host cannot hold is one no value of this type is made of either. So
     * the refusal belongs to this type and leaves by its own abort, the way an exponent past its width
     * does. Reached instead by building the number, the host says it by an exception of its arithmetic,
     * which says nothing about a Rational to whoever reads it (ADR-0112) and does not say it quickly: a
     * power of five the host has no room for is not refused on sight but computed until it does not fit,
     * which is minutes and hundreds of megabytes for an answer that was never going to come.
     *
     * <p>The count is under the truth rather than over it — a factor of five counted as two bits when it
     * is nearer two and a third — so this refuses nothing the host would have held, and what the
     * under-count lets through is refused by the host and translated where it is caught.
     */
    private static void heldByTheHost(long bits) {
        if (bits > Integer.MAX_VALUE) {
            throw new ConstraintViolation("no Rational holds a whole number of " + bits + " bits");
        }
    }

    /** That a whole number is one this type stores, which {@link #STORED_BITS} says why it bounds. */
    private static void heldByTheRepresentation(BigInteger part) {
        if (part != null && part.bitLength() > STORED_BITS) {
            throw new ConstraintViolation(
                    "no Rational holds a numerator or a denominator of " + part.bitLength() + " bits");
        }
    }

    /**
     * A count of bits as the host takes one, and the run's shortage where it is past what the host counts.
     *
     * <p>Every count of bits formed here goes through this. A bit length and a working width are both
     * {@code int}, so a count made of two of them is an {@code int} by default and wraps in silence — and
     * what a wrapped count does is not refuse but answer: a negative shift shifts the other way, and a
     * bracket whose ends were built that way holds the wrong numbers. A width settled beforehand kept those
     * counts small enough for the wrap to be unreachable; a width that rises until the host will not hold
     * the next one does not, so the arithmetic that forms them is the arithmetic that has to say so.
     *
     * <p>The shortage is the run's ({@link OutOfRoom}) rather than a value refused, because what these
     * counts are counting is an instrument. {@link #heldByTheHost} asks the same question about the parts a
     * value is made of, where the answer is that the value has no representation.
     */
    static int bitsTheHostAddresses(long bits) {
        if (bits > Integer.MAX_VALUE) {
            throw new OutOfRoom("this run has no room for a whole number of " + bits + " bits");
        }
        return (int) bits;
    }

    /**
     * The abort a whole number the host had no range for leaves by.
     *
     * <p>Every method of this type that computes translates it, and the translation is here rather than
     * at the operators in {@link RationalMath} because it is here that the host is reached: a list folded
     * with {@code List.sum} asks this type for a sum directly, so a translation at the operator alone
     * would leave the fold answering with an exception of the host's arithmetic.
     */
    private static ConstraintViolation noRoomForIt(ArithmeticException thrown) {
        return new ConstraintViolation("no Rational holds a whole number that size: " + thrown.getMessage());
    }

    /** Two exponents subtracted, or the abort of a computation asking for one past what is held. The
     *  difference of two exponents is the quotient's as much as their sum is the product's, so it is
     *  held to the same width and leaves it the same way — and never by an exception of the arithmetic
     *  it was computed with, which says nothing about a Rational to whoever reads it. */
    private static long lessened(long exponent, long by) {
        try {
            return Math.subtractExact(exponent, by);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Rational exponent out of range: " + exponent + " - " + by);
        }
    }

    /** Two exponents added, or the abort of a computation asking for one past what is held. Sixty-four
     *  bits is the exponent's width, and a value needing more of it has no representation here rather
     *  than a rounded one. */
    private static long added(long exponent, long by) {
        try {
            return Math.addExact(exponent, by);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Rational exponent out of range: " + exponent + " + " + by);
        }
    }

    /** An exponent negated, which the least sixty-four-bit number is not. */
    private static long negated(long exponent) {
        try {
            return Math.negateExact(exponent);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Rational exponent out of range: -(" + exponent + ")");
        }
    }

    /** An exponent as a power something is about to be built to. A power of two past what a positive
     *  {@code int} counts is one no machine holds the digits of, so it aborts here rather than
     *  answering a number it could not have built. */
    private static int buildable(long exponent) {
        if (exponent < 0 || exponent > Integer.MAX_VALUE) {
            throw new ConstraintViolation("no Rational is built at a power of " + exponent);
        }
        return (int) exponent;
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
                    numerator.multiply(raised(added(twos, scale), added(fives, scale))), scale);
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
            return numerator.multiply(raised(twos, fives));
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    /**
     * This as a decimal of {@code scale} places, rounded by {@code towards}.
     *
     * <p>Where a caller must have a decimal whatever the value is.
     *
     * <p><b>The scale goes to the exponents, not the digits.</b> A decimal of {@code scale} places is a
     * whole number over {@code 10^scale}, so what is asked for is the whole number this rounds to when
     * multiplied by that power — and multiplying by it moves the two exponents. So the rounding is done
     * on the factored value and the answer is that whole number beside the scale it was asked at.
     *
     * <p>Not a decimal built and then rounded. What a value's own exponents say has nothing to do with
     * how large the answer is: a value made of a power of two over a power of five that all but cancel
     * stands near one, and spelling it out first asks for digits the answer does not have and no machine
     * holds. Which is the same reason the order is answered from brackets, and the brackets are what
     * this reads too.
     */
    public BigDecimal asDecimal(int scale, java.math.RoundingMode towards) {
        if (isZero()) {
            return new BigDecimal(BigInteger.ZERO, scale);
        }
        try {
            return new BigDecimal(roundedTimesTenTo(scale, towards), scale);
        } catch (ArithmeticException e) {
            throw noRoomForIt(e);
        }
    }

    /**
     * The whole number {@code this × 10^scale} rounds to by {@code towards}, which is the unscaled value
     * of this at that scale.
     *
     * <p>Multiplying by the power of ten adds the scale to both exponents, and the sum is held wider than
     * an exponent is: a value whose own exponent is at the end of its range has an ordinary answer at an
     * ordinary scale, so this is one of the places where what an intermediate holds must not be what the
     * answer is allowed to be.
     *
     * <p>Two shapes are read off the exponents rather than bracketed, because a bracket can never say
     * that a value <i>is</i> a whole number or <i>is</i> exactly half of one, and the policies part
     * company at exactly half. In lowest terms with no two and no five left beside the fraction, the
     * value is a whole number exactly where the denominator is one and both exponents have reached
     * nought, and it is half of one exactly where the same holds of twice it.
     */
    private BigInteger roundedTimesTenTo(int scale, java.math.RoundingMode towards) {
        BigInteger byTwos = atTenTo(twos, scale);
        BigInteger byFives = atTenTo(fives, scale);
        // The two ends of the rounding come first, because a bracket cannot reach them: it says the value
        // stands between two whole numbers and never that it is one of them, nor that it stands at exactly
        // half of the way — and the policies part company at both. In lowest terms beside a fraction
        // holding no two and no five, the value is a whole number exactly where the denominator is one and
        // both exponents have reached nought, and half of one exactly where that holds of twice it.
        BigInteger magnitude = numerator.abs();
        boolean overOne = denominator.equals(BigInteger.ONE);
        if (overOne && byTwos.signum() >= 0 && byFives.signum() >= 0) {
            return signedLike(builtFrom(magnitude, byTwos, byFives));
        }
        // Twice the value, so that one whole number carries both which two it stands between and which
        // side of half of the way it stands: its half is the one, its last bit the other.
        BigInteger byTwiceTheTwos = byTwos.add(BigInteger.ONE);
        if (overOne && byTwiceTheTwos.signum() >= 0 && byFives.signum() >= 0) {
            return roundedFrom(
                    builtFrom(magnitude, byTwiceTheTwos, byFives).shiftRight(1), 0, towards);
        }
        BigInteger quickly = roundedFromBracketsAt(byTwiceTheTwos, byFives, towards, BRACKET_BITS);
        if (quickly != null) {
            return quickly;
        }
        // The bracket left two whole numbers in it, so the value stands close to half of the way between
        // them. Where the powers can be written down, writing them down answers exactly — at whatever
        // closeness the value happens to have, which is the shape no width settled on beforehand reaches.
        BigInteger exactly = roundedExactly(byTwos, byFives, towards);
        if (exactly != null) {
            return exactly;
        }
        // The value cannot be written out and the first bracket left it undecided, so the width rises. Which
        // way a value rounds is where it stands against half of the way between two whole numbers, and that
        // is an order — so it is refined by what refines the order, and for the same reason.
        return asWideAsItTakes(
                width -> roundedFromBracketsAt(byTwiceTheTwos, byFives, towards, width),
                () -> "round " + this);
    }

    /**
     * The whole number this rounds to at those exponents, read off one division of the value written out.
     *
     * <p>The value is written out once and read once. The whole part is the quotient, and where the value
     * stands against half of the way is where the remainder stands against half the denominator — one
     * fraction against another, answered by the same walk the order uses. Nothing is doubled on top of
     * that: doubling the remainder would ask for a number a bit larger than one already stored, which is
     * the bit the host does not have at its own end. What writing the value out costs is asked about
     * before it is done, the powers landing on whichever side their signs send them to.
     */
    private @Nullable BigInteger roundedExactly(
            BigInteger byTwos, BigInteger byFives, java.math.RoundingMode towards) {
        BigInteger @Nullable [] written = allWrittenOut(bitsAWritingIsWorth(storedBits()),
                new ToWriteOut(numerator.abs(), byTwos, byFives),
                new ToWriteOut(denominator, byTwos.negate(), byFives.negate()));
        if (written == null) {
            return null;
        }
        BigInteger up = written[0];
        BigInteger down = written[1];
        BigInteger[] whole = up.divideAndRemainder(down);
        if (whole[1].signum() == 0) {
            // A whole number, so there is no fraction for a policy to have an opinion about.
            return signedLike(whole[0]);
        }
        return roundedFrom(whole[0],
                comparedAsFractions(whole[1], down, BigInteger.ONE, HALVES), towards);
    }

    /** The whole number this rounds to as far as a bracket of {@code width} bits settles it, and null
     *  where the bracket holds two of them. */
    private @Nullable BigInteger roundedFromBracketsAt(
            BigInteger byTwiceTheTwos, BigInteger byFives, java.math.RoundingMode towards, int width) {
        Bracketed twice = bracketed(byTwiceTheTwos, byFives, width);
        BigInteger least = flooredFraction(twice.low(), BigInteger.ONE, twice.shift());
        BigInteger most = flooredFraction(twice.high(), BigInteger.ONE, twice.shift());
        return least.equals(most)
                ? roundedFrom(least.shiftRight(1), least.testBit(0) ? 1 : -1, towards)
                : null;
    }

    /**
     * Which of {@code whole} and the next one up the value rounds to, the value standing {@code
     * againstHalf} of the way between them and neither being reached exactly.
     *
     * <p>Every policy of the seven reads the sign and that standing and nothing else, which is what makes
     * the digits beside the point. At exactly half of the way the two neighbours are this whole number
     * and the next, and the policy that takes the even one takes whichever of those is even.
     *
     * <p>The eighth of the host's policies is not one of the seven and asks for no rounding at all, and it
     * is reached only where rounding is what the value needs — a value exact at the scale asked for is
     * answered above this, off its own exponents. So it refuses the way a caller's mistake is refused, and
     * not by an exception of the arithmetic: the abort a number too large leaves by is that, so a refusal
     * spelled the same way would be read as one, and a policy asking for something else would come back
     * saying the host had no room.
     */
    private BigInteger roundedFrom(
            BigInteger whole, int againstHalf, java.math.RoundingMode towards) {
        boolean awayFromNought = switch (towards) {
            case UP -> true;
            case DOWN -> false;
            case CEILING -> signum() > 0;
            case FLOOR -> signum() < 0;
            case HALF_UP -> againstHalf >= 0;
            case HALF_DOWN -> againstHalf > 0;
            case HALF_EVEN -> againstHalf > 0 || (againstHalf == 0 && whole.testBit(0));
            case UNNECESSARY -> throw new IllegalArgumentException(
                    "this value is not the decimal asked for, and no rounding was named: " + this);
        };
        return signedLike(awayFromNought ? whole.add(BigInteger.ONE) : whole);
    }

    /** An exponent with a scale added, held wider than an exponent is — the scale reaches every value
     *  this type holds, so their sum is not bounded by what one of them is. */
    private static BigInteger atTenTo(long exponent, int scale) {
        return BigInteger.valueOf(exponent).add(BigInteger.valueOf(scale));
    }

    /** {@code whole × 2^twos × 5^fives}, both exponents being at least nought. What this builds is the
     *  answer's own digits, which is the one thing a narrowing is always allowed to ask for. */
    private static BigInteger builtFrom(BigInteger whole, BigInteger twos, BigInteger fives) {
        int byTwos = buildable(twos);
        int byFives = buildable(fives);
        heldByTheHost(whole.bitLength() + byTwos + 2L * byFives);
        return whole.shiftLeft(byTwos).multiply(FIVE.pow(byFives));
    }

    /**
     * {@code floor(up × 2^byBits / down)}, {@code up} being at least nought and {@code down} above it.
     *
     * <p>Exact, and nothing here is larger than the answer or than what it was handed. Moved up, what is
     * built is the answer's own digits, which is the one size a narrowing may always ask for. Moved down,
     * the numerator comes down rather than the denominator going up — a floor of a floor over the same two
     * numbers is the floor of the two together — so the distance comes out of a number that has it to
     * give. Down by more bits than the numerator has, the value is below one and the floor is nought, and
     * the distance itself is one no count of bits holds.
     */
    private static BigInteger flooredFraction(BigInteger up, BigInteger down, BigInteger byBits) {
        if (byBits.signum() >= 0) {
            return up.shiftLeft(buildable(byBits)).divide(down);
        }
        BigInteger by = byBits.negate();
        if (by.compareTo(BigInteger.valueOf(up.bitLength())) > 0) {
            return BigInteger.ZERO;
        }
        return up.shiftRight(by.intValueExact()).divide(down);
    }

    /** The same of an exponent held wider than one of this type's own, which the sum of an exponent and
     *  a scale is. */
    private static int buildable(BigInteger exponent) {
        if (exponent.signum() < 0 || exponent.bitLength() > Integer.SIZE - 1) {
            throw new ConstraintViolation("no Rational is built at a power of " + exponent);
        }
        return exponent.intValueExact();
    }

    /** A magnitude given this value's sign. */
    private BigInteger signedLike(BigInteger magnitude) {
        return signum() < 0 ? magnitude.negate() : magnitude;
    }

    /** The numerator with the powers that multiply it built in. */
    private BigInteger numeratorWithItsPowers() {
        return numerator.multiply(raised(atLeastNought(twos), atLeastNought(fives)));
    }

    /** The denominator with the powers that divide it built in. */
    private BigInteger denominatorWithItsPowers() {
        return denominator.multiply(raised(atLeastNought(negated(twos)), atLeastNought(negated(fives))));
    }

    /** {@code e} where it is above nought, and nought where it is not. */
    private static long atLeastNought(long e) {
        return Math.max(e, 0);
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
