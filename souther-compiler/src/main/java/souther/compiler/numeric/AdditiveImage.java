package souther.compiler.numeric;

import java.util.Map;
import java.util.function.Function;

/**
 * The values a form {@code Σ cᵢ·xᵢ} can actually add up to.
 *
 * <p>Not the order its positions sit on. Read off the order alone, {@code 3 * a} over decimals was
 * taken to reach one — and it does not: a decimal is a finite decimal, a third does not terminate,
 * and no decimal a model writes is one. So {@code 3 * a <= 1} and {@code 3 * a < 1} admit the same
 * values, {@code 3 * a = 1} admits none, and a bound derived at a third is a bound at a value
 * nothing stands on.
 *
 * <p>Two generators, by what the positions are made of. Over positions that step, Bézout's: the form
 * takes exactly the whole multiples of {@code gcd(cᵢ)}. Over positions whose values fill, the whole
 * multiples of that divisor by a finite decimal — which is dense and is still not every number, since
 * ten is a unit among the finite decimals and a divisor with a factor of three is not.
 *
 * <p><b>Answering wider than the truth is safe here, and answering narrower is not.</b> All three
 * things this is asked — whether a value is reached, where a cut has to move to, whether an equality
 * can hold — get safer as the image gets bigger: a value outside a superset is outside the image, a
 * cut not moved is a cut that refuses nothing, and an equality refused because its value is outside
 * even the superset is an equality nothing satisfies. Which is why nothing here is asked to say how
 * exact it is.
 *
 * <p>A form whose positions are not all made of the same thing needs no coarser answer, as it turns
 * out. One position that fills is enough to make the whole sum fill: whole numbers are finite
 * decimals, and a finite decimal may be chosen with as many places as the value being reached asks
 * for, so the divisor generates the same set either way.
 */
public sealed interface AdditiveImage {

    /** What the form's values are whole (or finite-decimal) multiples of. Always positive. */
    Rational generator();

    /** Whether the form can add up to this value. */
    boolean contains(Rational value);

    /**
     * The tightest cut admitting exactly the values of this image that {@code cut} admits.
     *
     * <p>Where the form steps, a bound between two of its values moves down onto the one below —
     * which is what makes {@code a < 3} into {@code a <= 2} over whole numbers, and is the same rule
     * one level up. Where its values fill, a bound at a value the form does not reach cannot move
     * anywhere: there is no greatest value below it. What it can say is that the value itself is out,
     * which is why an unreachable bound comes back strict.
     */
    RationalCut tightenUpper(RationalCut cut);

    /** The same on the other side. */
    RationalCut tightenLower(RationalCut cut);

    /**
     * Which values of a position leave a residue this image reaches — {@code { x | t - c·x ∈ this }}.
     *
     * <p>The generating side of {@link #contains}. A search that only asks whether a residue is
     * reached can reject a value it has already chosen, and where a position offers one candidate a
     * rejection leaves nothing; asked this way the same arithmetic names the values worth choosing.
     *
     * <p>What comes back is a coset of whatever the position is made of, which is why the spacing is
     * an argument rather than read off this. An image over whole numbers is asked about by a position
     * whose values fill wherever a form's positions are not all spaced alike — and the two mixed
     * pairings are answered by the whole of the position's own values, which is wider than the truth
     * and safe for the reason given on this interface. Every caller today weighs positions that share
     * a carrier, so the mixed pairings are answered rather than refused and are not searched over.
     *
     * @param coefficient this position's weight in the form, never zero
     * @param target      what the positions from this one on still owe
     * @param source      how this position's own values are spaced
     */
    AffinePreimage affinePreimage(Rational coefficient, Rational target, Granularity source);

    /**
     * The image of {@code Σ coefs·atom} over positions spaced as {@code spacing} says.
     *
     * @param coefs   never empty and never zero-valued: a form that names no position is a constant,
     *                and what a constant comparison settles is decided before anything asks this
     * @param spacing how each named position's values are spaced. Required rather than defaulted for
     *                the reason {@link NumericDomain#assume} requires it — a position whose spacing
     *                is guessed is one a bound is either wrongly sharpened on or silently left blunt
     */
    static <A> AdditiveImage of(Map<A, Rational> coefs, Function<A, Granularity> spacing) {
        if (coefs.isEmpty()) {
            throw new IllegalArgumentException("a form with no positions adds up to nothing to ask about");
        }
        Rational divisor = Rational.ZERO;
        boolean anyFills = false;
        boolean anySteps = false;
        for (Map.Entry<A, Rational> each : coefs.entrySet()) {
            if (each.getValue().isZero()) {
                throw new IllegalArgumentException(
                        "a position with a zero coefficient is one the form does not name: " + each.getKey());
            }
            Granularity how = spacing.apply(each.getKey());
            if (how == null) {
                throw new IllegalStateException("no granularity given for `" + each.getKey() + "`");
            }
            anyFills |= how == Granularity.DENSE;
            anySteps |= how == Granularity.DISCRETE;
            divisor = Rational.gcd(divisor, each.getValue());
        }
        if (!anyFills) {
            return new OverWholeNumbers(divisor);
        }
        // Whole numbers are finite decimals, so one position that fills makes the whole sum fill,
        // and the divisor generates the same set as it would over positions that all fill. `x + 3y`
        // with `x` whole and `y` a decimal does reach a tenth — at `x = -2, y = 0.7` — because the
        // decimal may be chosen with as many places as the value asks for.
        return new OverFiniteDecimals(divisor);
    }

    /**
     * The largest value every one of {@code coefs} is a whole multiple of.
     *
     * <p>Split out from {@link #of} because two callers want the divisor without wanting the set: a
     * quantity written {@code 300s + 600c} is three hundred times the quantity {@code s + 2c}, and
     * turning a level written in one into the other divides by exactly this. Zero for no
     * coefficients — nothing constrains a divisor of nothing, and the caller that asks reads the
     * zero rather than being refused, which is the difference between this and {@link #of}.
     */
    static Rational divisorOf(Iterable<Rational> coefs) {
        Rational divisor = Rational.ZERO;
        for (Rational each : coefs) {
            divisor = Rational.gcd(divisor, each);
        }
        return divisor;
    }

    /** Every whole multiple of the generator, which is what a form over positions that step takes. */
    record OverWholeNumbers(Rational generator) implements AdditiveImage {

        public OverWholeNumbers {
            if (generator == null || generator.signum() <= 0) {
                throw new IllegalArgumentException("a divisor is positive: " + generator);
            }
        }

        @Override
        public boolean contains(Rational value) {
            return value.dividedBy(generator).isWhole();
        }

        @Override
        public RationalCut tightenUpper(RationalCut cut) {
            Rational steps = cut.at().dividedBy(generator);
            java.math.BigInteger below = cut.inclusive() || !steps.isWhole()
                    ? steps.floor()
                    : steps.floor().subtract(java.math.BigInteger.ONE);
            return RationalCut.inclusive(generator.times(Rational.of(below)));
        }

        @Override
        public RationalCut tightenLower(RationalCut cut) {
            Rational steps = cut.at().dividedBy(generator);
            java.math.BigInteger above = cut.inclusive() || !steps.isWhole()
                    ? steps.ceiling()
                    : steps.ceiling().add(java.math.BigInteger.ONE);
            return RationalCut.inclusive(generator.times(Rational.of(above)));
        }

        /**
         * The solutions of {@code c·x ≡ t (mod g)}, found the way Bézout's are.
         *
         * <p>With {@code d} the divisor of the coefficient and the generator, the residue has to be
         * a whole multiple of {@code d} or no value of the position leaves one this reaches — which
         * is the same test a search makes to prune, said as a set rather than as a rejection. Where
         * it passes, {@code c/d} and {@code g/d} share nothing, so the coefficient has an inverse
         * modulo the second and the solutions are one residue class of it.
         */
        @Override
        public AffinePreimage affinePreimage(Rational coefficient, Rational target,
                                             Granularity source) {
            if (source != Granularity.DISCRETE) {
                // A position that fills, weighed against a residue that steps. What works out is
                // `(t - g·k)/c` for whole `k`, which is a progression the position's values pass
                // through — and it is a progression whether or not its members are whole. Answered
                // before with every value the position has, on the ground that no caller weighed
                // positions spaced differently; one that does is a search with nothing to go on.
                //
                // Wider than the truth only in that a member may be no decimal a model writes,
                // which the position refuses when it is asked for that member.
                return new AffinePreimage.Stepping(target.dividedBy(coefficient),
                        generator.dividedBy(coefficient).abs(), source);
            }
            Rational divisor = Rational.gcd(coefficient, generator);
            Rational steps = target.dividedBy(divisor);
            if (!steps.isWhole()) {
                return new AffinePreimage.None();
            }
            java.math.BigInteger modulus = generator.dividedBy(divisor).numerator();
            if (modulus.equals(java.math.BigInteger.ONE)) {
                return new AffinePreimage.Stepping(Rational.ZERO, Rational.ONE, source);
            }
            java.math.BigInteger weight = coefficient.dividedBy(divisor).numerator().mod(modulus);
            java.math.BigInteger at = steps.numerator()
                    .multiply(weight.modInverse(modulus))
                    .mod(modulus);
            return new AffinePreimage.Stepping(Rational.of(at), Rational.of(modulus), source);
        }
    }

    /**
     * Every finite-decimal multiple of the generator.
     *
     * <p>What a form over positions whose values fill takes, and — for a form whose positions are
     * not all of one kind — a set holding what it takes rather than exactly it. Which of the two it
     * is nothing asks: all three things an image is used for get safer as it gets bigger, so the
     * wider answer needs no announcing. A reader that had to certify exactness would need telling
     * apart, and there is no such reader.
     */
    record OverFiniteDecimals(Rational generator) implements AdditiveImage {

        /**
         * With the units taken out of the generator, so that two divisors generating one set are one
         * value.
         *
         * <p>Here rather than at the callers. Six and three generate the same finite decimals — two
         * is a unit — and a caller that handed over the six unreduced would be told that three is not
         * a value the form reaches. That is a wrong answer rather than a coarse one, and it is not
         * one a caller should have to know to avoid.
         */
        public OverFiniteDecimals {
            if (generator == null || generator.signum() <= 0) {
                throw new IllegalArgumentException("a divisor is positive: " + generator);
            }
            generator = generator.unitsRemoved();
        }

        @Override
        public boolean contains(Rational value) {
            return value.dividedBy(generator).asWrittenDecimal() != null;
        }

        /**
         * Where the value is reached, the cut is already as tight as it goes; where it is not, there
         * is no greatest value below it to move to and the two ways of writing the cut admit the same
         * values — so what is left to say is that the value itself is out.
         */
        @Override
        public RationalCut tightenUpper(RationalCut cut) {
            return contains(cut.at()) ? cut : RationalCut.exclusive(cut.at());
        }

        @Override
        public RationalCut tightenLower(RationalCut cut) {
            return contains(cut.at()) ? cut : RationalCut.exclusive(cut.at());
        }

        /**
         * The values of the position leaving a residue this reaches, which are dense and are not all
         * of them.
         *
         * <p>Written {@code c/g = m/n} in lowest terms, what the position contributes is the coset
         * {@code (m/n)·D}, and a residue lands in this image exactly where {@code t/g} is a finite
         * decimal once multiplied by {@code n}. Two and five drop out of {@code n} first: they are
         * units among the finite decimals, so a position held to a multiple of two is held to nothing
         * — which is the same reduction {@link #OverFiniteDecimals} makes of its own generator, and
         * making it in one place and not the other is what would let the two disagree.
         *
         * <p>The value named is {@code n·(t/g)} moved by the inverse of {@code m}, and it is itself
         * a finite decimal wherever there is one at all: {@code n} differs from the reduced {@code n}
         * by units, and an inverse is a whole number.
         */
        @Override
        public AffinePreimage affinePreimage(Rational coefficient, Rational target,
                                             Granularity source) {
            if (source != Granularity.DENSE) {
                // The other mixed pairing: a position that steps, against a residue that fills.
                // A whole `x` works out where `(t - c·x)/g` is a written decimal, and multiplying
                // through by what the position's weight brings in leaves one residue class of the
                // part of it that is neither two nor five — the same reduction this image makes of
                // its own generator, since twos and fives are units among the finite decimals.
                Rational per = coefficient.dividedBy(generator);
                Rational owed = target.dividedBy(generator);
                java.math.BigInteger spread =
                        Rational.of(per.numerator()).unitsRemoved().numerator().abs();
                if (spread.equals(java.math.BigInteger.ONE)) {
                    return new AffinePreimage.Stepping(Rational.ZERO, Rational.ONE, source);
                }
                java.math.BigDecimal reached =
                        owed.times(Rational.of(per.denominator())).asWrittenDecimal();
                if (reached == null) {
                    return new AffinePreimage.None();
                }
                // `x ≡ (t/g)·den(c/g) · inverse(num(c/g)) (mod spread)`, taken over the whole
                // numbers: the member is a decimal here and the position holds whole numbers, so a
                // target that is no whole multiple leaves this position nothing.
                Rational at = Rational.of(reached).times(
                        Rational.of(Rational.of(per.numerator()).unitsRemoved().numerator()
                                .mod(spread).modInverse(spread)));
                if (!at.isWhole()) {
                    return new AffinePreimage.None();
                }
                return new AffinePreimage.Stepping(at, Rational.of(spread), source);
            }
            Rational per = coefficient.dividedBy(generator);
            Rational owed = target.dividedBy(generator);
            java.math.BigInteger spread = Rational.of(per.denominator()).unitsRemoved().numerator();
            if (owed.times(Rational.of(spread)).asWrittenDecimal() == null) {
                return new AffinePreimage.None();
            }
            java.math.BigInteger shift = spread.equals(java.math.BigInteger.ONE)
                    ? java.math.BigInteger.ZERO
                    : per.numerator().mod(spread).modInverse(spread);
            Rational at = owed.times(Rational.of(per.denominator())).times(Rational.of(shift));
            return new AffinePreimage.Filling(at, Rational.of(spread));
        }
    }
}
