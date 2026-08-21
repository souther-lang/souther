package souther.compiler.numeric;

import java.util.Map;
import java.util.function.Function;

/**
 * One thing the rules say about a weighted sum of positions, canonical.
 *
 * <p>Three shapes, and they are the three a comparison comes to: the sum is held below something,
 * held at something, or held away from it. Which of the six ways an author wrote it is gone by the
 * time one of these exists — {@code a >= 3} and {@code -a <= -3} are one constraint, and so are
 * {@code 300s + 600c <= 4800} and {@code s + 2c <= 16}.
 *
 * <p><b>What is settled here is settled by the constraint alone.</b> Reading one asks what the sum
 * can add up to ({@link AdditiveImage}) and nothing else — not what else has been asserted, not what
 * is known so far, not what order anything arrived in. So {@code 3 * a = 1} over decimals is
 * impossible the moment it is read, because no decimal is a third; {@code 2x + 2y <= 3} over whole
 * numbers is {@code x + y <= 1}, because the sum is whole and cannot sit between; and
 * {@code 3 * a <= 1} is {@code 3 * a < 1}, because the sum comes arbitrarily close to one and never
 * arrives. None of the three depends on anything but the rule itself, which is what keeps them out
 * of the part that has to be recomputed as more is learned.
 *
 * <p>Compared by what it says. Two writings of one rule are one constraint and one key, which is
 * what makes asserting a rule twice the same as asserting it once. Where a rule came from is not
 * part of that and is carried beside it, because a rule written in two places is still one rule and
 * two origins.
 */
public sealed interface AffineConstraint<A> {

    /** The sum this is about. */
    CanonicalForm<A> form();

    /**
     * The half-spaces this constraint states.
     *
     * <p>Asked of the constraint because it is the constraint's own answer. Three readers wanted it
     * — the difference bounds, to make edges; the reduction, to read each rule against a box; the
     * proof, to turn a question into something to bound — and each had written it out, so "an
     * equality is a bound above and a bound below" was said three times and could have been said
     * three ways.
     *
     * <p>A hole states none. Which side of it a sum lies is not something the rule says: it is
     * something the rest of what is known says, and it is answered where that can be read.
     */
    default java.util.List<HalfSpace<A>> halfSpaces() {
        return switch (this) {
            case HalfSpace<A> half -> java.util.List.of(half);
            case Equality<A> at -> java.util.List.of(
                    new HalfSpace<>(at.form(), RationalCut.inclusive(at.at())),
                    new HalfSpace<>(at.form().negated(), RationalCut.inclusive(at.at().negated())));
            case Disequality<A> hole -> java.util.List.of();
        };
    }

    /**
     * The same rule over positions called something else.
     *
     * <p>Here rather than at each shape, because renaming is one act and the three shapes differ
     * only in what they hold their sum against — and none of that moves when the positions are
     * called something else. Written per shape, a fourth shape would be one more place to remember
     * it, and the reading that forgot would hand back a rule about the positions it started with.
     *
     * <p>What is renamed is the form and never the threshold. A bound is a number and a number is
     * not in anybody's vocabulary.
     */
    default <B> AffineConstraint<B> over(Renaming<A, B> naming) {
        return switch (this) {
            case HalfSpace<A> half -> new HalfSpace<>(half.form().over(naming), half.bound());
            case Equality<A> at -> new Equality<>(at.form().over(naming), at.at());
            case Disequality<A> hole -> new Disequality<>(hole.form().over(naming), hole.at());
        };
    }

    /** The sum held no higher than a bound it may or may not reach. */
    record HalfSpace<A>(CanonicalForm<A> form, RationalCut bound) implements AffineConstraint<A> {

        public HalfSpace {
            if (form == null || bound == null) {
                throw new IllegalArgumentException("a half-space is a sum and a bound");
            }
        }

        @Override
        public String toString() {
            return form + " " + bound;
        }
    }

    /** The sum held at one value. */
    record Equality<A>(CanonicalForm<A> form, Rational at) implements AffineConstraint<A> {

        public Equality {
            if (form == null || at == null) {
                throw new IllegalArgumentException("an equality is a sum and a value");
            }
        }

        /**
         * Held at a value, whichever way round it was written.
         *
         * <p>{@code a = 3} and {@code -a = -3} are one rule, and a comparison says so by turning
         * around — {@code a >= 3} and {@code -a <= -3} come to the same half-space. An equality has
         * no direction to turn, so the two writings would otherwise be two records and the same rule
         * said twice would be two rules.
         *
         * <p>No reader depends on which of the two is held: what is built from an equality is built
         * from both sides of it.
         */
        @Override
        public boolean equals(Object other) {
            return other instanceof Equality<?> it && oneRuleEitherWayRound(this, it);
        }

        @Override
        public int hashCode() {
            return sameEitherWayRound(form, at);
        }

        @Override
        public String toString() {
            return form + " = " + at;
        }
    }

    /**
     * The sum held away from one value.
     *
     * <p>A hole and not a bound, which is why it is its own shape rather than something turned into
     * one on the way in. Turning it into a bound needs to know which side of the hole the sum is
     * already on, and that is not something the rule says — it is something the rest of what is
     * known says, and it can become known long after this arrived. Deciding it here is what made
     * {@code x /= 0} beside {@code x >= 0} leave {@code x} at nought or above depending on which was
     * written first.
     */
    record Disequality<A>(CanonicalForm<A> form, Rational at) implements AffineConstraint<A> {

        public Disequality {
            if (form == null || at == null) {
                throw new IllegalArgumentException("a disequality is a sum and a value");
            }
        }

        /** Held away from a value, whichever way round it was written; see {@link Equality}. */
        @Override
        public boolean equals(Object other) {
            return other instanceof Disequality<?> it && oneRuleEitherWayRound(this, it);
        }

        @Override
        public int hashCode() {
            return sameEitherWayRound(form, at);
        }

        @Override
        public String toString() {
            return form + " /= " + at;
        }
    }

    /**
     * Whether two of these say one thing, up to which way round it was written.
     *
     * <p>A comparison reduces {@code a >= 3} and {@code -a <= -3} to one half-space by turning one
     * of them around. Held at a value and held away from one have no direction to turn, so the two
     * writings are made one here instead — and here rather than in each of them, because it is one
     * fact about both.
     *
     * <p>Not settled by picking a canonical side, which would need an order over the positions that
     * a caller naming them is under no obligation to have. Two values, identified.
     */
    private static boolean oneRuleEitherWayRound(AffineConstraint<?> one, AffineConstraint<?> other) {
        Rational mine = valueOf(one);
        Rational theirs = valueOf(other);
        return one.form().equals(other.form()) && mine.equals(theirs)
                || one.form().equals(other.form().negated()) && mine.equals(theirs.negated());
    }

    private static Rational valueOf(AffineConstraint<?> constraint) {
        return switch (constraint) {
            case Equality<?> at -> at.at();
            case Disequality<?> hole -> hole.at();
            case HalfSpace<?> half -> half.bound().at();
        };
    }

    /** A number the same for a form and its negation, so the two writings hash alike. */
    private static <A> int sameEitherWayRound(CanonicalForm<A> form, Rational at) {
        return (form.hashCode() ^ form.negated().hashCode()) * 31
                + (at.hashCode() ^ at.negated().hashCode());
    }

    /**
     * What an assertion comes to once it has been read.
     *
     * <p>Three answers because a comparison need not be a constraint at all. A comparison of two
     * constants settles itself; so does one whose threshold is a value its sum cannot reach. Handing
     * back a constraint that says nothing, or one that says everything, would leave every reader
     * downstream to notice — and a reader that failed to notice would be holding a rule it could not
     * discharge.
     */
    sealed interface Read<A> {

        /** The constraint the assertion states. */
        record Stated<A>(AffineConstraint<A> constraint) implements Read<A> {}

        /** Every value satisfies it, so there is nothing to record. */
        record HoldsAlways<A>() implements Read<A> {}

        /** No value satisfies it. */
        record HoldsNever<A>() implements Read<A> {}
    }

    /**
     * The assertion {@code Σ coefs·atom + constant  rel  0}, read.
     *
     * @param spacing how each named position's values are spaced, for the same reason
     *                {@link NumericDomain#assume} wants it: a position whose spacing is guessed is
     *                one a bound is either wrongly sharpened on or silently left blunt
     */
    static <A> Read<A> of(Map<A, Rational> coefs, Rational constant, NumericDomain.Rel rel,
                          Function<A, Granularity> spacing) {
        CanonicalForm.Scaled<A> scaled = CanonicalForm.of(coefs);
        if (scaled == null) {
            return settledByConstantAlone(constant, rel);
        }
        // `Σ c·x + k rel 0` is `Σ c·x rel -k`, and dividing both by what the coefficients share
        // leaves which side of the threshold a value falls on, since what they share is positive.
        Rational threshold = constant.negated().dividedBy(scaled.by());
        CanonicalForm<A> form = scaled.form();
        AdditiveImage reaches = form.imageOver(spacing);
        return switch (rel) {
            case LE -> below(form, reaches, RationalCut.inclusive(threshold));
            case LT -> below(form, reaches, RationalCut.exclusive(threshold));
            // Turned around rather than given a shape of its own: `f >= t` is `-f <= -t`. The image
            // is the same one — what a sum reaches is closed under negation, since a multiple of the
            // divisor stays one when it changes sign — so only the form and the bound turn around.
            case GE -> below(form.negated(), reaches, RationalCut.inclusive(threshold.negated()));
            case GT -> below(form.negated(), reaches, RationalCut.exclusive(threshold.negated()));
            case EQ -> reaches.contains(threshold)
                    ? new Read.Stated<>(new Equality<>(form, threshold))
                    : new Read.HoldsNever<>();
            case NE -> reaches.contains(threshold)
                    ? new Read.Stated<>(new Disequality<>(form, threshold))
                    : new Read.HoldsAlways<>();
        };
    }

    /** A sum held below a bound, with the bound moved onto what the sum can actually reach. */
    private static <A> Read<A> below(CanonicalForm<A> form, AdditiveImage reaches, RationalCut at) {
        return new Read.Stated<>(new HalfSpace<>(form, reaches.tightenUpper(at)));
    }

    /** A comparison naming no position, which is arithmetic rather than a rule about anybody. */
    private static <A> Read<A> settledByConstantAlone(Rational constant, NumericDomain.Rel rel) {
        int sign = constant.signum();
        boolean holds = switch (rel) {
            case LE -> sign <= 0;
            case LT -> sign < 0;
            case GE -> sign >= 0;
            case GT -> sign > 0;
            case EQ -> sign == 0;
            case NE -> sign != 0;
        };
        return holds ? new Read.HoldsAlways<>() : new Read.HoldsNever<>();
    }
}
