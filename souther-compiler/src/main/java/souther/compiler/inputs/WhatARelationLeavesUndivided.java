package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
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
 * <p>The ends where a type's representation stops are not values a model divides. {@code x < y} is
 * false at the greatest {@code x} an {@code Int} holds whatever {@code y} is; that is where the
 * representation stops, and a run that stops only there is said with no end at all. Which ends
 * those are is the carrier's to say ({@code Carrier.asARelationReadsIt}): the last case of an
 * enumeration, the empty string and the last second of a day are values a model holds, so a run
 * a term takes ends there and a relation that comes out one way only there divides the place.
 * Reaching passes over an end only where what the reaching term has to stand at is
 * the other term's own value — two terms weighed one and minus one, held against nought — so that
 * every value it is needed at is a value of the type. Moved by a weight, an end of the type is a
 * value whose partner is past the end, and so is every value from half the way there on: under
 * {@code 2x - y < 0} an {@code x} past half the greatest {@code Int} needs a {@code y} past the
 * greatest. Moved by a
 * constant alone the same holds of the values as near the end as the constant is, and those are
 * passed over by the other reading, of how far apart two values moved together are
 * ({@link #ofTheirDifference}), and not by this one. And even where reaching passes over it, it is
 * so of the value at a place, which is one value there, and not of what an operation answers:
 * every pair holding the least {@code Int} is one {@code Int.min} answers the least of, and none
 * of them is below {@code d < Int.min(s, t)}'s {@code d}. So where an order needs the reaching
 * term past
 * an end the other runs to, the end is passed over only where the other is the value at its
 * place.
 *
 * <p>An order needs the reaching term strictly past each value it has to stand at on one side
 * only. {@code x < y} at {@code y} needs some {@code x} below it, where the comparison holds, and
 * some {@code x} at it or above, where it does not; which side is the strict one follows from the
 * relation and the sign of the term's weight.
 *
 * <p>Asked of the terms and not of how a reading came to them, so every reading that says a
 * relation divides no place asks these questions, over whatever it names its places by.
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
     * @param realizes a run every value of which it is shown to take, or null where none is shown.
     *                 Each end is one it takes, or, where its values are dense, one some value it
     *                 takes is as near as any other value asked of: so a value beyond an end is
     *                 one it takes, and an end that is not taken matters only where it is the
     *                 value asked of
     * @param takes    what values it takes, compared with another term's by equality — null where
     *                 nothing says
     * @param itsPlace whether it is the value at its one place, so that an end of its type it runs
     *                 to is one value there and not every value something answers it at
     */
    public record Term<P>(List<P> madeOf, ExactRatio weight, NumericDomain.Bounds holds,
                          NumericDomain.Bounds realizes, Object takes, boolean itsPlace) {

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
     * @param independent whether nothing ties where the term at one place in {@code terms} lies to
     *                    where the term at another does
     */
    public static <P> Set<P> of(List<Term<P>> terms, ExactRatio constant, Rel relation,
                                BiPredicate<P, P> overlap, Independence independent) {
        Set<P> out = new LinkedHashSet<>();
        for (int at = 0; at < terms.size(); at++) {
            if (reachedBySome(terms, at, constant, relation, overlap, independent)) {
                out.addAll(terms.get(at).madeOf());
            }
        }
        return out;
    }

    /**
     * What a relation leaves the values of one term it is written over: every value of it still
     * leaving the relation either way, or some runs of them settling it.
     *
     * <p>A value of a term settles the relation where it comes out one way whatever the others
     * hold — {@code n <= String.length(s)} holds at every {@code n} at or below nought, and
     * {@code p * q >= 1000} fails at {@code p} nought. That is shown of where the others may lie,
     * which is everything they could be. The values left are then asked what a term that is apart
     * reaches, as {@link #of} asks it, so a value neither shown to settle the relation nor shown to
     * leave it is no answer at all.
     */
    public sealed interface Leaves {

        /** Every value the term may hold leaves the relation coming out either way. */
        record Undivided() implements Leaves {}

        /**
         * Some runs of the term's values settle the relation whatever the rest hold, and every
         * other value it may hold leaves the relation either way.
         *
         * @param runs     the runs, in order, and none beside another that settles it the same way
         * @param least    the least value the term may hold, or null where it holds no least
         * @param greatest the greatest, or null where it holds no greatest
         */
        record Settled(List<SettledRun> runs, BigInteger least, BigInteger greatest)
                implements Leaves {

            public Settled {
                runs = List.copyOf(runs);
                if (runs.isEmpty()) {
                    throw new IllegalArgumentException("a term some values of which settle a"
                            + " relation has some");
                }
            }

            /**
             * The lines on the term that part its values where the relation is settled from where
             * it is not, or settled one way from settled the other: one where a run ends inside
             * what the term holds, and one value singled out where a run of one value has values
             * left either way on both sides of it — or null where two of them would say the same
             * of the term, which no two lines of one rule on one term may.
             */
            public List<Line> lines() {
                List<Line> out = new ArrayList<>();
                // The least value no run before has taken, or none where nothing bounds it below.
                BigInteger next = least;
                for (int i = 0; i < runs.size(); i++) {
                    SettledRun run = runs.get(i);
                    SettledRun after = i + 1 < runs.size() ? runs.get(i + 1) : null;
                    // Values it does not settle, just below it and just above it.
                    boolean leftBelow = run.from() != null
                            && (next == null || run.from().compareTo(next) > 0);
                    boolean leftAbove = run.to() != null && (after != null
                            ? after.from().compareTo(run.to().add(BigInteger.ONE)) > 0
                            : greatest == null || run.to().compareTo(greatest) < 0);
                    if (leftBelow && leftAbove && run.from().equals(run.to())) {
                        out.add(new Line(Rel.EQ, run.from()));
                    } else {
                        if (leftBelow) {
                            out.add(new Line(Rel.GE, run.from()));
                        }
                        // Above it, values it leaves, or the next run settling it the other way.
                        if (leftAbove || after != null) {
                            out.add(new Line(Rel.LE, run.to()));
                        }
                    }
                    next = run.to() == null ? null : run.to().add(BigInteger.ONE);
                }
                for (int i = 0; i < out.size(); i++) {
                    for (int j = i + 1; j < out.size(); j++) {
                        if (out.get(i).relation() == out.get(j).relation()) {
                            return null;
                        }
                    }
                }
                return List.copyOf(out);
            }
        }
    }

    /**
     * One line on a term a relation's settled values are parted by: the term standing to
     * {@code at} as {@code relation}, which holds on the side of it the run is.
     */
    public record Line(Rel relation, BigInteger at) {}

    /**
     * A run of whole values of a term, and how the relation comes out at every one of them.
     *
     * @param from  the least of them, or null where the run has no least
     * @param to    the greatest of them, or null where it has no greatest
     * @param holds whether the relation holds there, or fails there
     */
    public record SettledRun(BigInteger from, BigInteger to, boolean holds) {

        public SettledRun {
            if (from != null && to != null && from.compareTo(to) > 0) {
                throw new IllegalArgumentException("a run holds some value: " + from + " to " + to);
            }
        }
    }

    /**
     * What {@code terms} held against {@code constant} as {@code relation} leave the values of the
     * term at {@code at} — or null where neither is shown.
     *
     * <p>Shown undivided as {@link #of} shows it. Otherwise, where the term's values are whole, the
     * values that settle the relation are worked out from where the other terms may lie: those at
     * which the term weighed and every sum the others could come to hold together, and those at
     * which they fail together. Those are runs at the ends of what the term holds, and the values
     * between are asked again, as one run, whether some other term reaches every value it would
     * have to stand at there.
     *
     * <p>A run is a class only where some row of it has a value. The form is the number the run
     * compares only at a row where every sum and every weighing the run does stays inside the type,
     * and a value of the term at which none does is no row of either side. So each run is asked
     * for one such row: its value nearest nought beside each other term's nearest nought, with the
     * weighed size of every number of the form, the constant among them, coming to no more than
     * the type's greatest value — so no sum of them, in whatever order the run adds them, passes
     * it. Where a run has none, nothing is shown.
     *
     * @param whole    whether the term's values are whole numbers
     * @param greatest the greatest value the type of the form holds, or null where it holds no
     *                 greatest
     */
    public static <P> Leaves leavesOf(List<Term<P>> terms, int at, ExactRatio constant,
                                      Rel relation, BiPredicate<P, P> overlap,
                                      Independence independent, boolean whole,
                                      BigInteger greatest) {
        if (reachedBySome(terms, at, constant, relation, overlap, independent)) {
            return new Leaves.Undivided();
        }
        Term<P> it = terms.get(at);
        WholeRun held = whole ? WholeRun.ofTheValues(it.holds()) : null;
        if (held == null || constant == null) {
            return null;
        }
        // What the others and the constant come to together, wherever they lie.
        Interval rest = Interval.at(constant);
        for (int i = 0; i < terms.size(); i++) {
            if (i == at) {
                continue;
            }
            Interval each = Interval.of(terms.get(i).holds());
            Interval weighed = each == null ? null : each.times(terms.get(i).weight());
            rest = weighed == null ? null : rest.plus(weighed);
            if (rest == null) {
                return null;
            }
        }
        List<SettledRun> runs = new ArrayList<>();
        WholeRun between = held;
        for (boolean holds : List.of(true, false)) {
            Rel asked = holds ? relation : relation.denied();
            for (WholeRun settling : settledBy(it.weight(), rest, asked)) {
                between = between == null ? null : between.without(settling);
                WholeRun here = settling.meet(held);
                if (here.holdsAWholeNumber()) {
                    runs.add(new SettledRun(here.low, here.high, holds));
                }
            }
        }
        if (runs.isEmpty() || between == null) {
            return null;
        }
        if (greatest != null) {
            // The weighed size of every number but the term's, each at its value nearest nought.
            ExactRatio others = constant.abs();
            for (int i = 0; i < terms.size() && others != null; i++) {
                ExactRatio near = i == at ? ExactRatio.ZERO
                        : nearestNought(Interval.of(terms.get(i).holds()));
                ExactRatio sofar = others;
                others = near == null ? null : near.times(terms.get(i).weight().abs())
                        .flatMap(sofar::plus).orNull();
            }
            ExactRatio besideIt = others;
            for (SettledRun each : runs) {
                ExactRatio near = nearestNought(new Interval(
                        each.from() == null ? null : ExactRatio.of(each.from()),
                        each.to() == null ? null : ExactRatio.of(each.to())));
                ExactRatio total = besideIt == null || near == null ? null
                        : near.times(it.weight().abs()).flatMap(besideIt::plus).orNull();
                if (total == null || total.compareTo(ExactRatio.of(greatest)) > 0) {
                    return null;
                }
            }
        }
        if (between.holdsAWholeNumber()) {
            List<Term<P>> narrowed = new ArrayList<>(terms);
            narrowed.set(at, new Term<>(it.madeOf(), it.weight(), between.asBounds(),
                    it.realizes(), it.takes(), it.itsPlace()));
            if (!reachedBySome(narrowed, at, constant, relation, overlap, independent)) {
                return null;
            }
        }
        return new Leaves.Settled(inOrder(runs), held.low, held.high);
    }

    /**
     * What a product of the terms {@code it} and {@code other}, held against {@code level} as
     * {@code relation}, leaves the values of {@code it} — or null where neither is shown.
     *
     * <p>Fixing a value of {@code it} leaves a form of {@code other} weighed by that value, so each
     * value of it is asked what the form of the other is asked: whether it holds wherever the other
     * may lie, fails wherever it may, or is left either way because the other reaches both sides of
     * the level over the value. The value's sign turns the side round, so the values below nought
     * and those above are asked apart, each a run along which the level over the value moves one
     * way; nought settles the relation by itself, the product being nought wherever the other is.
     * Between the runs that settle it, the values left are shown undivided where the other takes a
     * value strictly on the side the relation needs, and one on the other side, of every level over
     * a value there — which lie between the level over each end of the run, and over an end the run
     * has none of, nought.
     *
     * <p>A product past where its type stops is a run that aborts, and no row of either side. Every
     * value of the other the reaching needs lies within one of the level over the value, so its
     * product lies within the value of the level, and no further out than the value itself where
     * the value is further out than the level. So where twice the level is a value of the type,
     * none of those products is past where it stops, but the one of the least value there is with a
     * value below nought — which is the end of the type and not a value a relation divides, as for
     * every other relation here. Where it is not, nothing is shown.
     *
     * <p>Held equal or unequal, only against nought: a product is nought where either factor is,
     * and against any other level, which values of {@code it} leave the other a whole number to
     * stand at is which of them divide the level, a set no run says.
     *
     * @param apart    whether the other is apart from {@code it} and tied to it by nothing, which is
     *                 what it takes for what the other reaches to be asked
     * @param greatest the greatest value the type of the product holds, or null where it holds no
     *                 greatest
     */
    public static <P> Leaves leavesOfAProduct(Term<P> it, Term<P> other, ExactRatio level,
                                              Rel relation, boolean apart,
                                              BigInteger greatest) {
        if (greatest != null && !(level.abs().times(ExactRatio.of(2))
                instanceof ExactAnswer.Held<ExactRatio>(ExactRatio twice)
                && twice.compareTo(ExactRatio.of(greatest)) <= 0)) {
            return null;
        }
        boolean exactly = relation == Rel.EQ || relation == Rel.NE;
        if (exactly && level.signum() != 0) {
            return null;
        }
        WholeRun held = WholeRun.ofTheValues(it.holds());
        Interval lies = Interval.of(other.holds());
        if (held == null || lies == null) {
            return null;
        }
        List<SettledRun> runs = new ArrayList<>();
        WholeRun zero = new WholeRun(BigInteger.ZERO, BigInteger.ZERO).meet(held);
        if (zero.holdsAWholeNumber()) {
            runs.add(new SettledRun(BigInteger.ZERO, BigInteger.ZERO,
                    relation.holds(ExactRatio.ZERO.compareTo(level))));
        }
        for (int sign : List.of(-1, 1)) {
            WholeRun side = (sign < 0 ? new WholeRun(null, BigInteger.ONE.negate())
                    : new WholeRun(BigInteger.ONE, null)).meet(held);
            if (!side.holdsAWholeNumber()) {
                continue;
            }
            WholeRun between = side;
            for (boolean holds : List.of(true, false)) {
                WholeRun settling = settledByAFactor(sign, lies, level,
                        holds ? relation : relation.denied());
                if (settling == null) {
                    continue;
                }
                between = between == null ? null : between.without(settling);
                WholeRun here = settling.meet(side);
                if (here.holdsAWholeNumber()) {
                    runs.add(new SettledRun(here.low, here.high, holds));
                }
            }
            if (between == null) {
                return null;
            }
            if (between.holdsAWholeNumber() && !(apart && other.realizes() != null
                    && reachesOverAFactor(other.realizes(), between, sign, level, relation))) {
                return null;
            }
        }
        return runs.isEmpty() ? new Leaves.Undivided()
                : new Leaves.Settled(inOrder(runs), held.low, held.high);
    }

    /**
     * The values a factor of {@code sign} settles {@code relation} of the product at, as a run of
     * that sign's values — every one of them, or none, or those past a value — or null where none
     * do.
     *
     * <p>Wherever the other lies in {@code lies}, the product at one value of the factor runs
     * between that value times each end of where the other lies; the relation holds of all of them
     * where it holds of the least of them for {@code >} and {@code >=}, of the greatest for
     * {@code <} and {@code <=}, and of nought alone, for {@code ==} against nought, where nought is
     * all the other may be.
     */
    private static WholeRun settledByAFactor(int sign, Interval lies, ExactRatio level,
                                             Rel relation) {
        WholeRun every = new WholeRun(null, null);
        return switch (relation) {
            case EQ -> lies.low() != null && lies.high() != null && lies.low().signum() == 0
                    && lies.high().signum() == 0 ? every : null;
            case NE -> (lies.low() != null && lies.low().signum() > 0)
                    || (lies.high() != null && lies.high().signum() < 0) ? every : null;
            case GT, GE -> productOfAnEnd(sign > 0 ? lies.low() : lies.high(), sign > 0 ? -1 : 1,
                    sign, level, relation);
            case LT, LE -> productOfAnEnd(sign > 0 ? lies.high() : lies.low(), sign > 0 ? 1 : -1,
                    sign, level, relation);
        };
    }

    /**
     * The values of a factor of {@code sign} at which that value times {@code end} stands to
     * {@code level} as {@code relation}, or null where it is at none.
     *
     * @param past which way the end runs off where it is null: below every number, or above
     */
    private static WholeRun productOfAnEnd(ExactRatio end, int past, int sign, ExactRatio level,
                                           Rel relation) {
        if (end == null) {
            // Past every number, so the product is past every number the way the factor's sign
            // turns it.
            int product = past * sign;
            boolean stands = product > 0 ? relation == Rel.GT || relation == Rel.GE
                    : relation == Rel.LT || relation == Rel.LE;
            return stands ? new WholeRun(null, null) : null;
        }
        if (end.signum() == 0) {
            return relation.holds(ExactRatio.ZERO.compareTo(level)) ? new WholeRun(null, null)
                    : null;
        }
        WholeRun at = WholeRun.where(new OnTheDifference(end, level.negated(), relation));
        return at != null && at.holdsAWholeNumber() ? at : null;
    }

    /**
     * Whether a factor reaching {@code realized} stands strictly on the side {@code relation}
     * needs, and on the other side, of the level over every value of the run {@code between} of
     * the other factor's values of {@code sign} — or, held equal or unequal to nought, at nought
     * and away from it.
     */
    private static boolean reachesOverAFactor(NumericDomain.Bounds realized, WholeRun between,
                                              int sign, ExactRatio level, Rel relation) {
        if (relation == Rel.EQ || relation == Rel.NE) {
            OfNumbers nought = new OfNumbers(ExactRatio.ZERO, ExactRatio.ZERO);
            return nought.within(realized) && (realized.min() == null || realized.max() == null
                    || !(realized.min().at() instanceof Count low)
                    || !(realized.max().at() instanceof Count high)
                    || low.exactly().signum() < 0 || high.exactly().signum() > 0);
        }
        // The level over each end of the run, and nought over an end it has none of.
        ExactRatio one = overAnEnd(level, between.low);
        ExactRatio two = overAnEnd(level, between.high);
        if (one == null || two == null) {
            return false;
        }
        Run needed = one.compareTo(two) <= 0 ? new OfNumbers(one, two) : new OfNumbers(two, one);
        return needed.around(realized, strictlyBelow(relation, ExactRatio.of(sign)));
    }

    /** {@code level} over {@code end}, nought where there is no end, or null where it could not
     *  be held. */
    private static ExactRatio overAnEnd(ExactRatio level, BigInteger end) {
        if (end == null) {
            return ExactRatio.ZERO;
        }
        return level.dividedBy(ExactRatio.of(end)).orNull();
    }

    /**
     * The runs of whole values a term weighed {@code weight} settles {@code relation} at, wherever
     * the rest come to in {@code rest}: those at which the weighed term and every sum the rest
     * could be stand as {@code relation} to nought.
     */
    private static List<WholeRun> settledBy(ExactRatio weight, Interval rest, Rel relation) {
        List<WholeRun> out = new ArrayList<>();
        switch (relation) {
            case LT, LE -> addWhere(weight, rest.high(), relation, out);
            case GT, GE -> addWhere(weight, rest.low(), relation, out);
            case EQ -> {
                if (rest.low() != null && rest.high() != null
                        && rest.low().compareTo(rest.high()) == 0) {
                    addWhere(weight, rest.low(), Rel.EQ, out);
                }
            }
            case NE -> {
                addWhere(weight, rest.high(), Rel.LT, out);
                addWhere(weight, rest.low(), Rel.GT, out);
            }
        }
        return out;
    }

    /** The whole values {@code weight} times which, moved by {@code constant}, stand to nought as
     *  {@code relation}, added to {@code out} where there are some; nothing where the constant is
     *  past every number. */
    private static void addWhere(ExactRatio weight, ExactRatio constant, Rel relation,
                                 List<WholeRun> out) {
        if (constant == null) {
            return;
        }
        WholeRun at = WholeRun.where(new OnTheDifference(weight, constant, relation));
        if (at != null && at.holdsAWholeNumber()) {
            out.add(at);
        }
    }

    /** How far from nought the value of {@code run} nearest it is, or null where the run is no
     *  run of numbers. */
    private static ExactRatio nearestNought(Interval run) {
        if (run == null) {
            return null;
        }
        if (run.low() != null && run.low().signum() > 0) {
            return run.low();
        }
        if (run.high() != null && run.high().signum() < 0) {
            return run.high().abs();
        }
        return ExactRatio.ZERO;
    }

    /** {@code runs} in order of their values, each joined to the one beside it where the two
     *  settle the relation the same way. */
    private static List<SettledRun> inOrder(List<SettledRun> runs) {
        List<SettledRun> sorted = new ArrayList<>(runs);
        sorted.sort((one, two) -> one.from() == null ? -1 : two.from() == null ? 1
                : one.from().compareTo(two.from()));
        List<SettledRun> out = new ArrayList<>();
        for (SettledRun each : sorted) {
            SettledRun last = out.isEmpty() ? null : out.getLast();
            if (last != null && last.holds() == each.holds() && last.to() != null
                    && each.from() != null
                    && last.to().add(BigInteger.ONE).compareTo(each.from()) >= 0) {
                out.set(out.size() - 1, new SettledRun(last.from(), each.to(), last.holds()));
            } else {
                out.add(each);
            }
        }
        return out;
    }

    /** Whether some term apart from the one at {@code at}, and tied to it by nothing, reaches
     *  every value it would have to stand at for that one to be left undivided. */
    private static <P> boolean reachedBySome(List<Term<P>> terms, int at, ExactRatio constant,
                                             Rel relation, BiPredicate<P, P> overlap,
                                             Independence independent) {
        for (int other = 0; other < terms.size(); other++) {
            if (other != at && apart(terms, other, overlap) && untied(terms, other, independent)
                    && reaches(terms, other, at, constant, relation)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether nothing ties where one term of a relation lies to where another does, asked of where
     * the two are in the relation's terms: what ties them is the caller's to say, and two terms
     * the same in every way it hands over may be tied differently.
     */
    @FunctionalInterface
    public interface Independence {

        boolean between(int one, int other);
    }

    /**
     * One statement about the difference of two terms: {@code weight} times the first less the
     * second, with {@code constant}, held against nought as {@code relation}.
     */
    public record OnTheDifference(ExactRatio weight, ExactRatio constant, Rel relation) {

        public OnTheDifference {
            if (weight == null || weight.signum() == 0 || constant == null || relation == null) {
                throw new IllegalArgumentException("a statement about a difference weighs it by"
                        + " something other than nought and holds it against a number");
            }
        }
    }

    /**
     * The places of two terms, held against {@code constant} as {@code relation}, shown undivided
     * because the relation and everything {@code held} of the two are about their difference alone.
     *
     * <p>Two values that take the same values, each every value of its type, weighed by one
     * weight and its negation, are moved together by any amount and the relation comes out as it
     * did. Then where the first stands does not matter beside the second, only how far apart they
     * are: for every value of the first, the second stands at it moved by each difference the
     * statements leave, and the relation is left to come out either way wherever one difference
     * they leave holds it and another fails it. Moved up to an end of the type, a value finds
     * no partner past it; that is where the representation stops and not a line the model draws,
     * the same end the other reading passes over for two terms held against nought. A
     * statement that keeps the first from some values of its own is not about the difference, and
     * leaves the caller nothing to pass here.
     *
     * <p><b>The middle of the type has to see both.</b> A difference no two values of the type are
     * apart by is no difference anything comes out at, and one only values near the two ends are
     * apart by settles the relation for nearly every value. So each outcome is asked of a
     * difference a value halfway between the ends reaches both ways. Then every value that finds no
     * partner for one of the two is nearer an end than the middle is, and the values passed over
     * are the ones beside the ends, however far in the line puts them.
     *
     * <p>Asked of whole differences only, which every value of a type a term takes lies apart by
     * where its values are whole, and which a dense type holds as well: a difference left between
     * two whole numbers and at neither is passed over, and nothing is shown.
     *
     * @param terms   two terms, each the value at its place, taking every value of its type and
     *                the same values as the other — or nothing is shown
     * @param held    every statement the rows arriving hold of either term, each about their
     *                difference
     * @param extent  where the type the two take stops, open on a side it does not
     * @param overlap whether two places are one, or one is part of the other
     */
    public static <P> Set<P> ofTheirDifference(List<Term<P>> terms, ExactRatio constant,
                                               Rel relation, List<OnTheDifference> held,
                                               NumericDomain.Bounds extent,
                                               BiPredicate<P, P> overlap) {
        if (terms.size() != 2 || constant == null || !apart(terms, 0, overlap)
                || !moveTogether(terms.get(0), terms.get(1))) {
            return Set.of();
        }
        WholeRun left = WholeRun.reachedFromTheMiddleOf(extent);
        if (left == null) {
            return Set.of();
        }
        for (OnTheDifference each : held) {
            WholeRun where = WholeRun.where(each);
            if (where == null) {
                return Set.of();
            }
            left = left.meet(where);
        }
        OnTheDifference line = new OnTheDifference(terms.get(0).weight(), constant, relation);
        if (!left.comesOut(line, true) || !left.comesOut(line, false)) {
            return Set.of();
        }
        Set<P> out = new LinkedHashSet<>(terms.get(0).madeOf());
        out.addAll(terms.get(1).madeOf());
        return out;
    }

    /**
     * Whether two terms are moved together by any amount and stay what they are: each the value at
     * its place, taking every value of its type and the same values as the other, weighed by one
     * weight and its negation.
     */
    private static <P> boolean moveTogether(Term<P> one, Term<P> other) {
        return one.itsPlace() && other.itsPlace()
                && one.realizes() != null && one.realizes().saysNothing()
                && other.realizes() != null && other.realizes().saysNothing()
                && one.takes() != null && one.takes().equals(other.takes())
                && one.weight().plus(other.weight()) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio sum)
                && sum.signum() == 0;
    }

    /**
     * Whether the term at {@code by} stands wherever the relation needs it to for the term at
     * {@code of} to be left undivided.
     */
    private static <P> boolean reaches(List<Term<P>> terms, int by, int of, ExactRatio constant,
                                       Rel relation) {
        Term<P> reaching = terms.get(by);
        boolean exactly = relation == Rel.EQ || relation == Rel.NE;
        boolean itsValue = standsAtTheOthersValue(terms, constant);
        if (exactly && itsValue && sameValues(terms, by, of)) {
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
        // An end of the type moved by a constant or a weight is needed past the end.
        if ((needed.runsDown() || needed.runsUp()) && !itsValue) {
            return false;
        }
        if (exactly) {
            return needed.within(reaching.realizes());
        }
        boolean strictlyBelow = strictlyBelow(relation, reaching.weight());
        if ((strictlyBelow ? needed.runsDown() : needed.runsUp())
                && !othersAreTheirPlaces(terms, by)) {
            return false;
        }
        return needed.around(reaching.realizes(), strictlyBelow);
    }

    /**
     * Whether, where the term weighed {@code weight} has to stand at a value for {@code relation}
     * to come out either way, it has to stand strictly below it on one side — and otherwise
     * strictly above it. The relation holds the terms' sum against nought: with the weight
     * positive, the sum under {@code <} holds strictly below the value and fails at it or above,
     * and under {@code >=} fails strictly below it.
     */
    private static boolean strictlyBelow(Rel relation, ExactRatio weight) {
        boolean below = relation == Rel.LT || relation == Rel.GE;
        return (weight.signum() > 0) == below;
    }

    /** Whether every term but the one at {@code by} is the value at its place. */
    private static <P> boolean othersAreTheirPlaces(List<Term<P>> terms, int by) {
        for (int i = 0; i < terms.size(); i++) {
            if (i != by && !terms.get(i).itsPlace()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether each of two terms stands exactly at the other's value: two terms weighed one and
     * minus one, held against nought — or against a value that is no number, which only such two
     * are.
     */
    private static <P> boolean standsAtTheOthersValue(List<Term<P>> terms, ExactRatio constant) {
        return eachStandsAtTheOthersValue(terms.stream().map(Term::weight).toList(), constant);
    }

    /**
     * Whether terms weighed {@code weights} and held against {@code constant} each stand exactly at
     * the other's value: two of them, weighed one and minus one, held against nought or against a
     * value that is no number. Such two are two values of one order.
     */
    public static boolean eachStandsAtTheOthersValue(List<ExactRatio> weights,
                                                     ExactRatio constant) {
        if (weights.size() != 2 || (constant != null && constant.signum() != 0)) {
            return false;
        }
        ExactRatio one = weights.get(0);
        return one.abs().equals(ExactRatio.ONE)
                && one.plus(weights.get(1)) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio sum)
                && sum.signum() == 0;
    }

    /** Whether the two terms of a relation each standing at the other's value take the same
     *  values. */
    private static <P> boolean sameValues(List<Term<P>> terms, int by, int of) {
        Object takes = terms.get(by).takes();
        return takes != null && takes.equals(terms.get(of).takes());
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
        if (standsAtTheOthersValue(terms, constant)) {
            Term<P> other = terms.get(1 - by);
            return new OfPlaces(other.holds().min() == null ? null : other.holds().min().at(),
                    other.holds().max() == null ? null : other.holds().max().at());
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
        // Where the term's weight and the rest come to nought: the rest turned and over the weight.
        ExactRatio turned = ExactRatio.ONE.negated().dividedBy(reaching.weight()).orNull();
        Interval at = turned == null ? null : rest.times(turned);
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
    private static <P> boolean untied(List<Term<P>> terms, int at, Independence independent) {
        for (int other = 0; other < terms.size(); other++) {
            if (other != at && !independent.between(at, other)) {
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

        /** Whether {@code realized} holds, beside every value of this run, a value strictly below
         *  it and one at it or above — or, not {@code strictlyBelow}, one strictly above it and one
         *  at it or below. */
        default boolean around(NumericDomain.Bounds realized, boolean strictlyBelow) {
            return lowFrom(realized.min(), strictlyBelow) && highTo(realized.max(), !strictlyBelow);
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

    /** The whole numbers between two, each end inclusive and null where nothing bounds it. */
    private record WholeRun(BigInteger low, BigInteger high) {

        /**
         * The whole differences a value halfway between the ends of {@code extent} is apart from
         * some value of it by, either way — every one where it is open on a side — or null where an
         * end is no number.
         */
        static WholeRun reachedFromTheMiddleOf(NumericDomain.Bounds extent) {
            if (extent.min() == null || extent.max() == null) {
                return new WholeRun(null, null);
            }
            if (!(extent.min().at() instanceof Count low)
                    || !(extent.max().at() instanceof Count high)
                    || !(high.exactly().minus(low.exactly())
                            instanceof ExactAnswer.Held<ExactRatio>(ExactRatio across))
                    || !(across.dividedBy(ExactRatio.of(2)) instanceof ExactAnswer.Held<ExactRatio>(
                            ExactRatio half))
                    || !(half.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger reach))) {
                return null;
            }
            return new WholeRun(reach.negate(), reach);
        }

        /**
         * The whole differences {@code statement} holds at, or null where they are no run: a
         * difference held apart from one value, or a number this cannot write.
         */
        static WholeRun where(OnTheDifference statement) {
            // weight × d + constant against nought: d against the constant turned and over the
            // weight, the relation turned where the weight is negative.
            ExactRatio at = statement.constant().negated().dividedBy(statement.weight()).orNull();
            BigInteger floor = at == null ? null : at.floor().orNull();
            BigInteger ceiling = at == null ? null : at.ceiling().orNull();
            if (floor == null || ceiling == null) {
                return null;
            }
            Rel relation = statement.weight().signum() < 0 ? statement.relation().turned()
                    : statement.relation();
            return switch (relation) {
                case LT -> new WholeRun(null, ceiling.subtract(BigInteger.ONE));
                case LE -> new WholeRun(null, floor);
                case GT -> new WholeRun(floor.add(BigInteger.ONE), null);
                case GE -> new WholeRun(ceiling, null);
                case EQ -> at.isWhole() ? new WholeRun(floor, floor)
                        : new WholeRun(BigInteger.ONE, BigInteger.ZERO);
                case NE -> null;
            };
        }

        WholeRun meet(WholeRun other) {
            BigInteger lower = low == null ? other.low
                    : other.low == null ? low : low.max(other.low);
            BigInteger upper = high == null ? other.high
                    : other.high == null ? high : high.min(other.high);
            return new WholeRun(lower, upper);
        }

        /** The whole numbers {@code bounds} holds, or null where an end of it is no number. */
        static WholeRun ofTheValues(NumericDomain.Bounds bounds) {
            BigInteger lower = null;
            BigInteger upper = null;
            if (bounds.min() != null) {
                if (!(bounds.min().at() instanceof Count least)) {
                    return null;
                }
                lower = bounds.min().inclusive() ? least.exactly().ceiling().orNull()
                        : least.exactly().floor().map(at -> at.add(BigInteger.ONE)).orNull();
                if (lower == null) {
                    return null;
                }
            }
            if (bounds.max() != null) {
                if (!(bounds.max().at() instanceof Count most)) {
                    return null;
                }
                upper = bounds.max().inclusive() ? most.exactly().floor().orNull()
                        : most.exactly().ceiling().map(at -> at.subtract(BigInteger.ONE)).orNull();
                if (upper == null) {
                    return null;
                }
            }
            return new WholeRun(lower, upper);
        }

        /**
         * What is left of this run with {@code taken} out of it, or null where what is left is two
         * runs: {@code taken} lies inside it and touches neither end.
         */
        WholeRun without(WholeRun taken) {
            if (!meet(taken).holdsAWholeNumber()) {
                return this;
            }
            boolean fromBelow = taken.low == null || (low != null && taken.low.compareTo(low) <= 0);
            boolean fromAbove = taken.high == null
                    || (high != null && taken.high.compareTo(high) >= 0);
            if (fromBelow && fromAbove) {
                return new WholeRun(BigInteger.ONE, BigInteger.ZERO);
            }
            if (fromBelow) {
                return new WholeRun(taken.high.add(BigInteger.ONE), high);
            }
            if (fromAbove) {
                return new WholeRun(low, taken.low.subtract(BigInteger.ONE));
            }
            return null;
        }

        /** This run as bounds on numbers, each end inclusive. */
        NumericDomain.Bounds asBounds() {
            return new NumericDomain.Bounds(
                    low == null ? null : Endpoint.inclusive(Count.of(new BigDecimal(low))),
                    high == null ? null : Endpoint.inclusive(Count.of(new BigDecimal(high))));
        }

        boolean holdsAWholeNumber() {
            return low == null || high == null || low.compareTo(high) <= 0;
        }

        /** Whether some whole number of this run is a difference {@code line} comes out
         *  {@code holding} at. */
        boolean comesOut(OnTheDifference line, boolean holding) {
            Rel relation = holding ? line.relation() : line.relation().denied();
            if (relation == Rel.NE) {
                WholeRun at = where(new OnTheDifference(line.weight(), line.constant(), Rel.EQ));
                return at != null && holdsAWholeNumber() && !equals(at);
            }
            WholeRun where = where(new OnTheDifference(line.weight(), line.constant(), relation));
            return where != null && meet(where).holdsAWholeNumber();
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

        Run asRun() {
            return new OfNumbers(low, high);
        }
    }
}
