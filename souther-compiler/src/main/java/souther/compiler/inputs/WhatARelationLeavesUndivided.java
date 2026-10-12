package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiPredicate;

/**
 * Which of the places a relation is written over it is shown to leave undivided.
 *
 * <p>A relation divides a place where some value of it settles how the relation comes out whatever
 * the rest hold: {@code n == String.length(s)} is false at every {@code n} below nought, and
 * {@code d == String.lowercase(s)} at every {@code d} holding a capital, because nothing on the
 * other side reaches those values. So that a relation leaves a place undivided is a claim about
 * what the other side reaches, and it is made only where it is shown: some other term of the
 * relation, apart from every other term's places and tied to none of them, is shown to take every
 * value it would have to stand at for the relation to come out either way — exactly the value the
 * rest comes to, for two values being one or not, and values on either side of it, for an order.
 *
 * <p><b>What a term may hold and what it is shown to take are two answers.</b> Where a value can
 * lie is an outer bound, and a term held to a run need not take every value inside it: a date
 * limited to the first days of 2020 and 2022 has its year between the two and never in 2021. So
 * the term reaching is asked of a run every value of which it is shown to take, and what it has to
 * reach is worked out from where the others may lie. Knowing a run is not filling it.
 *
 * <p>Two values taking the same values are each at every value the other is, which is a second way
 * a term reaches: {@code e.value == c.value} over two values of one declared type relates them and
 * divides neither. Not for an order: the least value a declaration leaves is one {@code x > y} is
 * false at, whatever {@code y} of the same declaration is.
 *
 * <p>The ends of a type are not values a model divides. {@code x < y} is false at the greatest
 * {@code x} an {@code Int} holds whatever {@code y} is, as it is at the least string under
 * {@code y < x}; that is where the representation stops, and a run that stops only there is said
 * with no end at all.
 *
 * <p>Asked of the terms and not of how a reading came to them, so every reading that says a
 * relation divides no place asks this one question, over whatever it names its places by.
 */
public final class WhatARelationLeavesUndivided {

    private WhatARelationLeavesUndivided() {
    }

    /**
     * One term of a relation.
     *
     * @param madeOf   the places its value is made of, in the order the relation names them
     * @param weight   what it is weighed by in the relation
     * @param holds    a run every value it may take lies in, open on a side nothing bounds it
     * @param realizes a run every value of which it is shown to take, or null where none is shown
     * @param takes    what values it takes, compared with another term's by equality — null where
     *                 nothing says
     */
    public record Term<P>(List<P> madeOf, ExactRatio weight, NumericDomain.Bounds holds,
                          NumericDomain.Bounds realizes, Object takes) {

        public Term {
            if (madeOf == null || weight == null || weight.signum() == 0 || holds == null) {
                throw new IllegalArgumentException("a term of a relation is made of something,"
                        + " weighed by something other than nought and held somewhere");
            }
            madeOf = List.copyOf(madeOf);
        }
    }

    /**
     * The places of {@code terms} that {@code terms} held against {@code constant} as
     * {@code relation} is shown to leave undivided.
     *
     * @param constant    what the terms are held against, or null where it is no number — a value
     *                    of the type the terms are values of, which only two terms weighed alike and
     *                    held against nought have
     * @param overlap     whether two places are one, or one is part of the other
     * @param independent whether nothing ties where one term lies to where another does
     */
    public static <P> Set<P> of(List<Term<P>> terms, ExactRatio constant, Rel relation,
                                BiPredicate<P, P> overlap,
                                BiPredicate<Term<P>, Term<P>> independent) {
        Set<P> out = new LinkedHashSet<>();
        for (int at = 0; at < terms.size(); at++) {
            for (int other = 0; other < terms.size(); other++) {
                if (other != at && apart(terms, other, overlap)
                        && untied(terms, other, independent)
                        && reaches(terms, other, at, constant, relation)) {
                    out.addAll(terms.get(at).madeOf());
                    break;
                }
            }
        }
        return out;
    }

    /**
     * Whether the term at {@code by} stands wherever the relation needs it to for the term at
     * {@code of} to be left undivided.
     */
    private static <P> boolean reaches(List<Term<P>> terms, int by, int of, ExactRatio constant,
                                       Rel relation) {
        Term<P> reaching = terms.get(by);
        boolean exactly = relation == Rel.EQ || relation == Rel.NE;
        if (exactly && sameValues(terms, by, of)) {
            return true;
        }
        if (reaching.realizes() == null) {
            return false;
        }
        if (exactly && !(reaching.weight().abs().equals(ExactRatio.ONE) && constant != null
                && constant.isWhole()
                && terms.stream().allMatch(each -> each.weight().isWhole()))) {
            return false;
        }
        Run needed = needed(terms, by, constant);
        if (needed == null) {
            return false;
        }
        return exactly ? needed.within(reaching.realizes())
                : needed.strictlyWithin(reaching.realizes());
    }

    /** Two values taking the same values, and nothing else in the relation. */
    private static <P> boolean sameValues(List<Term<P>> terms, int by, int of) {
        Term<P> reaching = terms.get(by);
        Term<P> reached = terms.get(of);
        return terms.size() == 2 && reaching.takes() != null
                && reaching.takes().equals(reached.takes())
                && reaching.weight().abs().equals(ExactRatio.ONE)
                && reached.weight().abs().equals(ExactRatio.ONE);
    }

    /**
     * Where the term at {@code by} has to stand for the relation to hold at its line, wherever the
     * rest lie: what the others and the constant come to, over the term's weight and turned — or
     * null where that is no run this can write.
     *
     * <p>A run of numbers where every end is a number, and otherwise only the one case a value no
     * number writes allows: two terms weighed one and minus one against nought, where the term has
     * to stand exactly where the other may.
     */
    private static <P> Run needed(List<Term<P>> terms, int by, ExactRatio constant) {
        Term<P> reaching = terms.get(by);
        if (terms.size() == 2 && (constant == null || constant.signum() == 0)) {
            Term<P> other = terms.get(1 - by);
            ExactAnswer<ExactRatio> sum = reaching.weight().plus(other.weight());
            if (reaching.weight().abs().equals(ExactRatio.ONE)
                    && sum instanceof ExactAnswer.Held<ExactRatio>(ExactRatio cancelled)
                    && cancelled.signum() == 0) {
                return new OfPlaces(other.holds().min() == null ? null : other.holds().min().at(),
                        other.holds().max() == null ? null : other.holds().max().at());
            }
        }
        if (constant == null) {
            return null;
        }
        // The sum of the others weighed, the constant with it, as a run of numbers.
        Interval rest = Interval.at(constant);
        for (int i = 0; i < terms.size(); i++) {
            if (i == by) {
                continue;
            }
            Interval each = Interval.of(terms.get(i).holds());
            if (each == null) {
                return null;
            }
            rest = rest.plus(each.times(terms.get(i).weight()));
            if (rest == null) {
                return null;
            }
        }
        Interval over = rest.times(reaching.weight().negated());
        Interval at = over == null ? null : over.over(reaching.weight().abs());
        return at == null ? null : at.asRun();
    }

    /** Whether no place of the term at {@code at} is one any other term is made of. */
    private static <P> boolean apart(List<Term<P>> terms, int at, BiPredicate<P, P> overlap) {
        for (int other = 0; other < terms.size(); other++) {
            if (other == at) {
                continue;
            }
            for (P one : terms.get(at).madeOf()) {
                for (P two : terms.get(other).madeOf()) {
                    if (overlap.test(one, two)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /** Whether nothing ties the term at {@code at} to any other. */
    private static <P> boolean untied(List<Term<P>> terms, int at,
                                      BiPredicate<Term<P>, Term<P>> independent) {
        for (int other = 0; other < terms.size(); other++) {
            if (other != at && !independent.test(terms.get(at), terms.get(other))) {
                return false;
            }
        }
        return true;
    }

    /**
     * A run of values a term would have to stand at, each end inclusive and absent where it runs
     * to the end of the type.
     */
    private interface Run {

        /** How an end of a run a term takes stands to this run's least value: below it is
         *  negative — or null where the two cannot be compared, or this run has no least value. */
        Integer againstTheLeast(Place end);

        /** The same, against this run's greatest value. */
        Integer againstTheGreatest(Place end);

        boolean runsDown();

        boolean runsUp();

        /** Whether {@code realized} holds every value of this run. */
        default boolean within(NumericDomain.Bounds realized) {
            return lowFrom(realized.min(), false) && highTo(realized.max(), false);
        }

        /** Whether {@code realized} holds values beyond this run at both ends, as well as all of
         *  it. */
        default boolean strictlyWithin(NumericDomain.Bounds realized) {
            return lowFrom(realized.min(), true) && highTo(realized.max(), true);
        }

        private boolean lowFrom(Endpoint end, boolean beyond) {
            if (end == null) {
                return true;
            }
            if (runsDown()) {
                return false;
            }
            Integer order = againstTheLeast(end.at());
            return order != null && (order < 0 || (order == 0 && !beyond && end.inclusive()));
        }

        private boolean highTo(Endpoint end, boolean beyond) {
            if (end == null) {
                return true;
            }
            if (runsUp()) {
                return false;
            }
            Integer order = againstTheGreatest(end.at());
            return order != null && (order > 0 || (order == 0 && !beyond && end.inclusive()));
        }
    }

    /** A run of values of any type, between two of them. */
    private record OfPlaces(Place min, Place max) implements Run {

        @Override
        public Integer againstTheLeast(Place end) {
            return end.compareTo(min);
        }

        @Override
        public Integer againstTheGreatest(Place end) {
            return end.compareTo(max);
        }

        @Override
        public boolean runsDown() {
            return min == null;
        }

        @Override
        public boolean runsUp() {
            return max == null;
        }
    }

    /** A run of numbers, which an end that is a number is compared with. */
    private record OfNumbers(ExactRatio min, ExactRatio max) implements Run {

        @Override
        public Integer againstTheLeast(Place end) {
            return end instanceof Count count ? count.exactly().compareTo(min) : null;
        }

        @Override
        public Integer againstTheGreatest(Place end) {
            return end instanceof Count count ? count.exactly().compareTo(max) : null;
        }

        @Override
        public boolean runsDown() {
            return min == null;
        }

        @Override
        public boolean runsUp() {
            return max == null;
        }
    }

    /** A run of numbers, each end inclusive and null where nothing bounds it. */
    private record Interval(ExactRatio low, ExactRatio high) {

        static Interval at(ExactRatio value) {
            return new Interval(value, value);
        }

        /** The run {@code bounds} gives, or null where an end is no number. */
        static Interval of(NumericDomain.Bounds bounds) {
            ExactRatio low = number(bounds.min());
            ExactRatio high = number(bounds.max());
            if ((bounds.min() != null && low == null) || (bounds.max() != null && high == null)) {
                return null;
            }
            return new Interval(low, high);
        }

        private static ExactRatio number(Endpoint end) {
            return end != null && end.at() instanceof Count count ? count.exactly() : null;
        }

        Interval plus(Interval other) {
            ExactRatio lower = low == null || other.low == null ? null
                    : low.plus(other.low).orNull();
            ExactRatio upper = high == null || other.high == null ? null
                    : high.plus(other.high).orNull();
            if ((low != null && other.low != null && lower == null)
                    || (high != null && other.high != null && upper == null)) {
                return null;
            }
            return new Interval(lower, upper);
        }

        Interval times(ExactRatio by) {
            ExactRatio one = low == null ? null : low.times(by).orNull();
            ExactRatio two = high == null ? null : high.times(by).orNull();
            if ((low != null && one == null) || (high != null && two == null)) {
                return null;
            }
            return by.signum() >= 0 ? new Interval(one, two) : new Interval(two, one);
        }

        Interval over(ExactRatio by) {
            ExactRatio one = low == null ? null : low.dividedBy(by).orNull();
            ExactRatio two = high == null ? null : high.dividedBy(by).orNull();
            if ((low != null && one == null) || (high != null && two == null)) {
                return null;
            }
            return new Interval(one, two);
        }

        Run asRun() {
            return new OfNumbers(low, high);
        }
    }
}
