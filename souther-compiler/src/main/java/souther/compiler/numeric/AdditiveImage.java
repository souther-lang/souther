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
 * even the superset is an equality nothing satisfies. So a form whose positions are not all made of
 * the same thing answers with the coarser of the two, and nothing has to be told that it did.
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
        // Whole numbers are finite decimals, so a form with some of each adds up inside the finite
        // decimals the whole form's divisor generates. Not exactly that set — `x + 3y` with `x` whole
        // and `y` a decimal reaches no tenth, though the divisor is one — and wider is the safe way
        // to be wrong here, so that is the answer rather than a narrower one it cannot stand behind.
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

    /**
     * What is left of a divisor once the factors a finite decimal can be divided by are taken out.
     *
     * <p>Ten is a unit among the finite decimals, so two and five are: dividing by either lands on a
     * finite decimal again, above and below the line alike. Taking them out is what makes two
     * divisors that generate one set one value — a quarter and a tenth both generate every decimal
     * there is, and so does one.
     */
    private static Rational unitsRemoved(Rational divisor) {
        java.math.BigInteger top = divisor.numerator().abs();
        java.math.BigInteger bottom = divisor.denominator();
        for (java.math.BigInteger unit : java.util.List.of(
                java.math.BigInteger.TWO, java.math.BigInteger.valueOf(5))) {
            while (top.mod(unit).signum() == 0) {
                top = top.divide(unit);
            }
            while (bottom.mod(unit).signum() == 0) {
                bottom = bottom.divide(unit);
            }
        }
        return Rational.of(top, bottom);
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
            generator = unitsRemoved(generator);
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
    }
}
