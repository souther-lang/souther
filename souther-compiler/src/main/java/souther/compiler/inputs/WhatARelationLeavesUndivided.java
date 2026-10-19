package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
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
     * @param spacing  how its values are spaced, or null where that is not said. Only a dense term
     *                 takes values as near as asked of an end its run leaves out
     */
    public record Term<P>(List<P> madeOf, ExactRatio weight, NumericDomain.Bounds holds,
                          NumericDomain.Bounds realizes, Object takes, boolean itsPlace,
                          Granularity spacing) {

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
            if (reachedBySome(terms, at, constant, relation, overlap, independent, null)) {
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
     *
     * <p><b>An answer about where the relation divides the term, and not about which rows can be
     * run.</b> The ends where the type stops are read as the class's account says: an end value
     * the relation comes out one way at only because its partner would pass where the type stops is
     * no class of the model's, as {@code x < y} draws no line at the greatest {@code x}. So
     * {@link Undivided} says the relation draws no line on the term, and not that every value the
     * type holds has a row on each side the run can hold: at the least {@code Int},
     * {@code x * y >= 1000} has none with {@code y} at minus one. Whether a row has a value the run
     * can hold is asked of the row, where the arithmetic is done in the type
     * ({@code OrderedAffineBoundary.productAt}); a reader wanting a row on each side for every
     * value asks that, and not this.
     */
    public sealed interface Leaves {

        /** The relation draws no line on the term: every value it may hold leaves the relation
         *  coming out either way, an end of the type read as the class's account reads it. */
        record Undivided() implements Leaves {}

        /**
         * Some runs of the term's values settle the relation whatever the rest hold, and every
         * other value it may hold leaves the relation either way.
         *
         * @param runs     the runs, in order, and none beside another that settles it the same way
         * @param least    the lower end of what the term may hold, or null where it holds no least
         * @param greatest the upper end, or null where it holds no greatest
         * @param whole    whether the term's values are whole numbers, so that a run ending at one
         *                 and a run starting at the next leave nothing between them
         */
        record Settled(List<SettledRun> runs, ExactCut least, ExactCut greatest, boolean whole)
                implements Leaves {

            /** Runs of a term whose values are whole, its ends being the whole numbers it holds. */
            public static Settled ofWhole(List<SettledRun> runs, BigInteger least,
                                          BigInteger greatest) {
                return new Settled(runs, least == null ? null : wholeEnd(least),
                        greatest == null ? null : wholeEnd(greatest), true);
            }

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
             * left either way on both sides of it. Several runs are several lines, and two of them
             * may stand to different values as the same relation.
             */
            public List<Line> lines() {
                List<Line> out = new ArrayList<>();
                // What the runs before cover, up to its upper end; none where nothing bounds the
                // term below.
                ExactCut covered = least == null ? null : justBelow(least);
                ExactCut afterTheLast = greatest == null ? null : justAbove(greatest);
                for (int i = 0; i < runs.size(); i++) {
                    SettledRun run = runs.get(i);
                    SettledRun after = i + 1 < runs.size() ? runs.get(i + 1) : null;
                    // Values it does not settle, just below it and just above it.
                    boolean leftBelow = run.from() != null
                            && (covered == null || gapBetween(covered, run.from(), whole));
                    boolean leftAbove = run.to() != null && (after != null
                            ? gapBetween(run.to(), after.from(), whole)
                            : afterTheLast == null || gapBetween(run.to(), afterTheLast, whole));
                    if (leftBelow && leftAbove && run.from().at().compareTo(run.to().at()) == 0) {
                        out.add(new Line(Rel.EQ, run.from().at()));
                    } else {
                        if (leftBelow) {
                            out.add(new Line(run.from().inclusive() ? Rel.GE : Rel.GT,
                                    run.from().at()));
                        }
                        // Above it, values it leaves, or the next run settling it the other way.
                        if (leftAbove || after != null) {
                            out.add(new Line(run.to().inclusive() ? Rel.LE : Rel.LT,
                                    run.to().at()));
                        }
                    }
                    covered = run.to();
                }
                return List.copyOf(out);
            }

            /** The upper end of everything below the lower end {@code from}, or null where it
             *  cannot be held. */
            private ExactCut justBelow(ExactCut from) {
                if (!whole) {
                    return new ExactCut(from.at(), !from.inclusive());
                }
                ExactRatio before = from.at().minus(ExactRatio.ONE).orNull();
                return before == null ? null : ExactCut.inclusive(before);
            }

            /** The lower end of everything above the upper end {@code to}, or null where it
             *  cannot be held. */
            private ExactCut justAbove(ExactCut to) {
                if (!whole) {
                    return new ExactCut(to.at(), !to.inclusive());
                }
                ExactRatio next = to.at().plus(ExactRatio.ONE).orNull();
                return next == null ? null : ExactCut.inclusive(next);
            }
        }
    }

    /** The end a whole number {@code at} is, inclusive. */
    private static ExactCut wholeEnd(BigInteger at) {
        return ExactCut.inclusive(ExactRatio.of(at));
    }

    /**
     * Whether a value lies between a run ending at {@code to} and one starting at {@code from}: a
     * whole number, or a decimal, as the term is spaced. Where that cannot be worked out there is
     * taken to be one, which keeps a line the runs would otherwise lose.
     */
    private static boolean gapBetween(ExactCut to, ExactCut from, boolean whole) {
        if (whole) {
            ExactRatio next = to.at().plus(ExactRatio.ONE).orNull();
            return next == null || from.at().compareTo(next) > 0;
        }
        int order = from.at().compareTo(to.at());
        if (order < 0) {
            return false;
        }
        if (order == 0) {
            return !to.inclusive() && !from.inclusive()
                    && Lattice.holds(Granularity.DENSE, to.at());
        }
        Lattice.Point after = Lattice.least(Granularity.DENSE,
                new ExactCut(to.at(), !to.inclusive()));
        Lattice.Point before = Lattice.greatest(Granularity.DENSE,
                new ExactCut(from.at(), !from.inclusive()));
        Integer placed = Lattice.compare(after, before);
        return placed == null || placed <= 0;
    }

    /**
     * One line on a term a relation's settled values are parted by: the term standing to
     * {@code at} as {@code relation}, which holds on the side of it the run is.
     */
    public record Line(Rel relation, ExactRatio at) {}

    /**
     * A run of values of a term, and how the relation comes out at every one of them.
     *
     * @param from  the lower end of the run, or null where it has no least
     * @param to    the upper end of the run, or null where it has no greatest
     * @param holds whether the relation holds there, or fails there
     */
    public record SettledRun(ExactCut from, ExactCut to, boolean holds) {

        public SettledRun {
            if (from != null && to != null && (from.at().compareTo(to.at()) > 0
                    || (from.at().compareTo(to.at()) == 0
                            && !(from.inclusive() && to.inclusive())))) {
                throw new IllegalArgumentException("a run holds some value: " + from + " to " + to);
            }
        }

        /** A run of the whole numbers {@code from} to {@code to}, either end null where it has
         *  none. */
        public static SettledRun whole(BigInteger from, BigInteger to, boolean holds) {
            return new SettledRun(from == null ? null : wholeEnd(from),
                    to == null ? null : wholeEnd(to), holds);
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
     * <p>Where the term's values are dense, the same is worked out over runs that end open or
     * closed, and the values left between the runs settled are as many runs as they come to, each
     * asked whether some other term reaches every value of it.
     *
     * @param granularity how the term's values are spaced, or null where they are no numbers
     * @param greatest    the greatest value the type of the form holds, or null where it holds no
     *                    greatest
     */
    public static <P> Leaves leavesOf(List<Term<P>> terms, int at, ExactRatio constant,
                                      Rel relation, BiPredicate<P, P> overlap,
                                      Independence independent, Granularity granularity,
                                      BigInteger greatest) {
        Jointly jointly = granularity == Granularity.DISCRETE && greatest != null
                ? new Jointly(greatest) : null;
        if (reachedBySome(terms, at, constant, relation, overlap, independent, jointly)) {
            return new Leaves.Undivided();
        }
        Term<P> it = terms.get(at);
        if (granularity == null || constant == null) {
            return null;
        }
        WholeRun held = granularity == Granularity.DISCRETE
                ? WholeRun.ofTheValues(it.holds()) : null;
        if (granularity == Granularity.DISCRETE && held == null) {
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
        if (granularity == Granularity.DENSE) {
            return leavesOfADenseTerm(terms, at, constant, relation, overlap, independent, rest);
        }
        List<SettledRun> runs = new ArrayList<>();
        WholeRun between = held;
        for (boolean holds : List.of(true, false)) {
            Rel asked = holds ? relation : relation.denied();
            for (OnTheDifference statement : settledBy(it.weight(), rest, asked)) {
                WholeRun settling = WholeRun.where(statement);
                if (settling == null || !settling.holdsAWholeNumber()) {
                    continue;
                }
                between = between == null ? null : between.without(settling);
                WholeRun here = settling.meet(held);
                if (here.holdsAWholeNumber()) {
                    runs.add(SettledRun.whole(here.low, here.high, holds));
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
                ExactRatio near = nearestNought(new Interval(each.from(), each.to()));
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
                    it.realizes(), it.takes(), it.itsPlace(), it.spacing()));
            if (!reachedBySome(narrowed, at, constant, relation, overlap, independent, jointly)) {
                return null;
            }
        }
        return Leaves.Settled.ofWhole(inOrder(runs, true), held.low, held.high);
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
     * <p>The ends where the type stops are read as a relation reads them (the class's account):
     * an end value the relation comes out one way at only because its partner would pass where the
     * type stops is no class, and a run of values that would is shown nothing. Every value of the
     * other the reaching needs lies within one of the level over the value, so its product lies
     * within the value of the level, and no further out than the value itself where the value is
     * further out than the level. So where twice the level is a value of the type, the one product
     * past where it stops is the least value's with minus one: the least value alone, which is the
     * end of the type, as {@code x < y} has no {@code y} past the greatest {@code x} and divides
     * nothing there. Where twice the level is past the type, a run of values would need such a
     * partner, and nothing is shown.
     *
     * <p>A run that settles the relation is a class only where some row of it has a value: its value
     * nearest nought times the other's nearest nought, which is the least product there is, must be
     * a value of the type, or the run is one every value of which stands only past where the type
     * stops, and nothing is shown.
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
            runs.add(SettledRun.whole(BigInteger.ZERO, BigInteger.ZERO,
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
                    runs.add(SettledRun.whole(here.low, here.high, holds));
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
        if (greatest != null) {
            ExactRatio nearOther = nearestNought(lies);
            for (SettledRun each : runs) {
                ExactRatio near = nearestNought(new Interval(each.from(), each.to()));
                ExactRatio smallest = near == null || nearOther == null ? null
                        : near.times(nearOther).orNull();
                if (smallest == null || smallest.compareTo(ExactRatio.of(greatest)) > 0) {
                    return null;
                }
            }
        }
        return runs.isEmpty() ? new Leaves.Undivided()
                : Leaves.Settled.ofWhole(inOrder(runs, true), held.low, held.high);
    }

    /**
     * What a remainder of {@code dividend} by {@code divisor} held equal or unequal to nought leaves
     * the values of one of them — or null where neither is shown.
     *
     * <p>Equal to nought it is {@code divisor | dividend}, with a divisor of nought outside what
     * any row stands at: the run stops there. Without a period to draw, which values settle it on
     * their own is what the other may hold, and it is shown only where that is a run.
     *
     * <p>A dividend settles it at nought, which every divisor divides, and at the values smaller in
     * size than every divisor, which none divides. That the divisors are every size from some one
     * up, and that the divisor reaches every size from there up on one side, is what shows every
     * other dividend leaves it either way: the divisor at its own size divides it, and one past its
     * size does not. A divisor settles it at one and minus one, which divide every dividend; the
     * rest leave it either way where the dividend may be nought or has no end, and two dividends
     * side by side are shown, one of which a divisor of any other size leaves undivided.
     *
     * @param askDividend whether the answer is about the dividend, or the divisor
     * @param apart       whether the other is apart from the one asked and tied to it by nothing
     * @param dividends   where the type of the dividend stops: a divisor of any size has a multiple
     *                    among the dividends only where they reach out from nought or from no
     *                    further than half the way to the end, as a weight does
     *                    ({@link #leavesOfAProduct}), and the divisors past what any dividend
     *                    reaches settle it unmet as a run of their own
     * @param divisors    where the type of the divisor stops: the dividend of the greatest size is
     *                    divided by a divisor of that size only if the type holds one
     */
    public static <P> Leaves leavesOfADivisibility(Term<P> dividend, Term<P> divisor,
                                                   boolean askDividend, Rel relation,
                                                   boolean apart, Ends dividends, Ends divisors) {
        if (!apart || (relation != Rel.EQ && relation != Rel.NE)) {
            return null;
        }
        boolean holdsWhenDivides = relation == Rel.EQ;
        List<SettledRun> runs = new ArrayList<>();
        WholeRun held;
        if (askDividend) {
            held = WholeRun.ofTheValues(dividend.holds());
            WholeRun sizes = WholeRun.ofTheValues(divisor.holds());
            BigInteger least = held == null || sizes == null ? null : leastSizeFromWhichEvery(sizes);
            if (least == null || !reachesEverySizeFrom(divisor.realizes(), least)
                    || !everyDividendHasADivisor(dividends, divisors, divisor.realizes(), least)) {
                return null;
            }
            WholeRun nought = new WholeRun(BigInteger.ZERO, BigInteger.ZERO).meet(held);
            if (nought.holdsAWholeNumber()) {
                runs.add(SettledRun.whole(BigInteger.ZERO, BigInteger.ZERO, holdsWhenDivides));
            }
            if (least.compareTo(BigInteger.ONE) > 0) {
                BigInteger below = least.subtract(BigInteger.ONE);
                for (WholeRun side : List.of(new WholeRun(below.negate(), BigInteger.ONE.negate()),
                        new WholeRun(BigInteger.ONE, below))) {
                    WholeRun here = side.meet(held);
                    if (here.holdsAWholeNumber()) {
                        runs.add(SettledRun.whole(here.low, here.high, !holdsWhenDivides));
                    }
                }
            }
        } else {
            held = WholeRun.ofTheValues(divisor.holds());
            WholeRun values = WholeRun.ofTheValues(dividend.holds());
            if (held == null || values == null || !twoInARow(values)
                    || !(containsNought(values) || values.low == null || values.high == null)
                    || dividend.realizes() == null) {
                return null;
            }
            WholeRun seen = WholeRun.ofTheValues(dividend.realizes());
            if (seen == null || !twoInARow(seen)
                    || !(containsNought(seen) || seen.low == null || seen.high == null)
                    || !reachesAMultipleOfEverySize(seen, dividends)) {
                return null;
            }
            for (BigInteger one : List.of(BigInteger.ONE.negate(), BigInteger.ONE)) {
                if (new WholeRun(one, one).meet(held).holdsAWholeNumber()) {
                    runs.add(SettledRun.whole(one, one, holdsWhenDivides));
                }
            }
            for (WholeRun beyond : divisorsBeyondEveryDividend(seen, dividends)) {
                WholeRun here = beyond.meet(new WholeRun(divisors.least(), divisors.greatest()))
                        .meet(held);
                if (here.holdsAWholeNumber()) {
                    runs.add(SettledRun.whole(here.low, here.high, !holdsWhenDivides));
                }
            }
        }
        return runs.isEmpty() ? new Leaves.Undivided()
                : Leaves.Settled.ofWhole(inOrder(runs, true), held.low, held.high);
    }

    /** The least size such that the divisors held in {@code divisors}, nought aside, are every
     *  whole number of that size or more on at least one sign — or null where they are not. */
    private static BigInteger leastSizeFromWhichEvery(WholeRun divisors) {
        if (divisors.high == null) {
            return divisors.low == null || divisors.low.signum() <= 0 ? BigInteger.ONE
                    : divisors.low;
        }
        if (divisors.low == null) {
            return divisors.high.signum() >= 0 ? BigInteger.ONE : divisors.high.negate();
        }
        return null;
    }

    /** Whether a term taking every value of {@code realizes} takes, on one sign, every size from
     *  {@code least} up. */
    private static boolean reachesEverySizeFrom(NumericDomain.Bounds realizes, BigInteger least) {
        WholeRun seen = realizes == null ? null : WholeRun.ofTheValues(realizes);
        if (seen == null) {
            return false;
        }
        return (seen.high == null && (seen.low == null || seen.low.compareTo(least) <= 0))
                || (seen.low == null && (seen.high == null
                        || seen.high.compareTo(least.negate()) >= 0));
    }

    /**
     * Whether a divisor of every size has a multiple among the dividends {@code seen}: where they
     * hold nought it has, and where they run off one way from an end it has one as long as the end
     * is no further than half the way to where the type stops — a divisor just under the end then
     * has its second multiple past it. The divisors with none are
     * {@link #divisorsBeyondEveryDividend}.
     */
    private static boolean reachesAMultipleOfEverySize(WholeRun seen, Ends dividends) {
        if (containsNought(seen)) {
            return true;
        }
        BigInteger stop = seen.low != null ? dividends.greatest()
                : dividends.least() == null ? null : dividends.least().negate();
        BigInteger end = seen.low != null ? seen.low : seen.high;
        return stop == null || end.abs().multiply(BigInteger.TWO).compareTo(stop) <= 0;
    }

    /**
     * The divisors that have no multiple among dividends running off one way from an end that
     * excludes nought: those whose size is past where the type of the dividend stops on the side
     * the multiple would fall. Each settles the relation unmet, whatever the dividend is.
     */
    private static List<WholeRun> divisorsBeyondEveryDividend(WholeRun seen, Ends dividends) {
        if (containsNought(seen)) {
            return List.of();
        }
        List<WholeRun> out = new ArrayList<>();
        if (seen.low != null) {
            BigInteger greatest = dividends.greatest();
            if (greatest != null) {
                out.add(new WholeRun(greatest.add(BigInteger.ONE), null));
                out.add(new WholeRun(null, greatest.negate().subtract(BigInteger.ONE)));
            }
        } else if (dividends.least() != null) {
            BigInteger least = dividends.least();
            out.add(new WholeRun(least.negate().add(BigInteger.ONE), null));
            out.add(new WholeRun(null, least.subtract(BigInteger.ONE)));
        }
        return out;
    }

    /**
     * Whether every dividend has, among the divisors the term takes, one of at least {@code least}
     * in size that divides it. The dividend is its own divisor where the type of the divisor holds
     * its size; the one value of the type's far end, a size past it, has half its size.
     */
    private static boolean everyDividendHasADivisor(Ends dividends, Ends divisors,
                                                    NumericDomain.Bounds realizes, BigInteger least) {
        WholeRun taken = WholeRun.ofTheValues(realizes);
        BigInteger size = dividends.greatest() == null || dividends.least() == null ? null
                : dividends.greatest().max(dividends.least().abs());
        List<BigInteger> reaches = new ArrayList<>();
        if (taken.high == null) {
            reaches.add(divisors.greatest());
        }
        if (taken.low == null) {
            reaches.add(divisors.least() == null ? null : divisors.least().negate());
        }
        for (BigInteger reach : reaches) {
            boolean ok = size == null ? reach == null
                    : reach == null || size.compareTo(reach) <= 0
                            || (size.equals(reach.add(BigInteger.ONE)) && !size.testBit(0)
                                    && size.shiftRight(1).compareTo(least) >= 0);
            if (ok) {
                return true;
            }
        }
        return false;
    }

    /** Where a type of whole numbers stops, either end null where it does not. */
    public record Ends(BigInteger least, BigInteger greatest) { }

    private static boolean twoInARow(WholeRun run) {
        return run.low == null || run.high == null || run.high.compareTo(run.low) > 0;
    }

    private static boolean containsNought(WholeRun run) {
        return (run.low == null || run.low.signum() <= 0)
                && (run.high == null || run.high.signum() >= 0);
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
            return nought.within(realized, Spacings.UNKNOWN)
                    && (realized.min() == null || realized.max() == null
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
        return needed.around(realized, strictlyBelow(relation, ExactRatio.of(sign)),
                Spacings.UNKNOWN);
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
    private static List<OnTheDifference> settledBy(ExactRatio weight, Interval rest,
                                                   Rel relation) {
        List<OnTheDifference> out = new ArrayList<>();
        switch (relation) {
            case LT, LE -> addWhere(weight, rest.upper(), relation, out);
            case GT, GE -> addWhere(weight, rest.lower(), relation, out);
            case EQ -> {
                if (rest.lower() != null && rest.upper() != null
                        && rest.low().compareTo(rest.high()) == 0
                        && rest.lower().inclusive() && rest.upper().inclusive()) {
                    addWhere(weight, rest.lower(), Rel.EQ, out);
                }
            }
            case NE -> {
                addWhere(weight, rest.upper(), Rel.LT, out);
                addWhere(weight, rest.lower(), Rel.GT, out);
            }
        }
        return out;
    }

    /** What {@code weight} times a value, moved by the end {@code constant}, standing to nought
     *  as {@code relation} says, added to {@code out}; nothing where the constant is past every
     *  number. A strict relation against an end the rest never reach holds as the relation that
     *  allows equality does. */
    private static void addWhere(ExactRatio weight, ExactCut constant, Rel relation,
                                 List<OnTheDifference> out) {
        if (constant == null) {
            return;
        }
        Rel asked = constant.inclusive() ? relation : switch (relation) {
            case LT -> Rel.LE;
            case GT -> Rel.GE;
            default -> relation;
        };
        out.add(new OnTheDifference(weight, constant.at(), asked));
    }

    /**
     * What a relation leaves the values of a dense term, which the runs that settle it, open or
     * closed, and the values left between them are asked of.
     */
    private static <P> Leaves leavesOfADenseTerm(List<Term<P>> terms, int at, ExactRatio constant,
                                                 Rel relation, BiPredicate<P, P> overlap,
                                                 Independence independent, Interval rest) {
        Term<P> it = terms.get(at);
        Span held = Span.ofTheValues(it.holds());
        if (held == null) {
            return null;
        }
        List<SettledRun> runs = new ArrayList<>();
        List<Span> between = List.of(held);
        for (boolean holds : List.of(true, false)) {
            Rel asked = holds ? relation : relation.denied();
            for (OnTheDifference statement : settledBy(it.weight(), rest, asked)) {
                Span settling = Span.where(statement);
                if (settling == null) {
                    continue;
                }
                Span.Occupancy settles = settling.occupancy();
                if (settles == Span.Occupancy.UNKNOWN) {
                    return null;
                }
                if (settles == Span.Occupancy.EMPTY) {
                    continue;
                }
                List<Span> left = new ArrayList<>();
                for (Span each : between) {
                    List<Span> remains = each.without(settling);
                    if (remains == null) {
                        return null;
                    }
                    left.addAll(remains);
                }
                between = left;
                Span here = settling.meet(held);
                Span.Occupancy within = here.occupancy();
                if (within == Span.Occupancy.UNKNOWN) {
                    return null;
                }
                if (within == Span.Occupancy.HOLDS) {
                    runs.add(new SettledRun(here.lower(), here.upper(), holds));
                }
            }
        }
        if (runs.isEmpty()) {
            return null;
        }
        for (Span each : between) {
            if (!reachedBySome(terms, at, new Interval(each.lower(), each.upper()), constant,
                    relation, overlap, independent, null)) {
                return null;
            }
        }
        return new Leaves.Settled(inOrder(runs, false), held.lower(), held.upper(), false);
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
    private static List<SettledRun> inOrder(List<SettledRun> runs, boolean whole) {
        List<SettledRun> sorted = new ArrayList<>(runs);
        sorted.sort((one, two) -> one.from() == null ? (two.from() == null ? 0 : -1)
                : two.from() == null ? 1 : one.from().at().compareTo(two.from().at()));
        List<SettledRun> out = new ArrayList<>();
        for (SettledRun each : sorted) {
            SettledRun last = out.isEmpty() ? null : out.getLast();
            if (last != null && last.holds() == each.holds() && last.to() != null
                    && each.from() != null && !gapBetween(last.to(), each.from(), whole)) {
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
                                             Independence independent, Jointly jointly) {
        return reachedBySome(terms, at, null, constant, relation, overlap, independent, jointly);
    }

    /**
     * The same, asked of the values of the term at {@code at} that lie in {@code within} and not
     * of all it may hold — an exact run, so that an end no decimal writes is still the end.
     */
    private static <P> boolean reachedBySome(List<Term<P>> terms, int at, Interval within,
                                             ExactRatio constant, Rel relation,
                                             BiPredicate<P, P> overlap,
                                             Independence independent, Jointly jointly) {
        boolean[] free = new boolean[terms.size()];
        for (int other = 0; other < terms.size(); other++) {
            free[other] = other != at && apart(terms, other, overlap)
                    && untied(terms, other, independent);
            if (free[other] && reaches(terms, other, at, within, constant, relation)) {
                return true;
            }
        }
        return within == null && reachedTogether(terms, at, constant, relation, free, jointly);
    }

    /**
     * What lets the others be asked together: the type of the relation's terms is whole numbers
     * and the arithmetic on them stops only past {@code greatest}, so a sum inside it is computed.
     * A type whose arithmetic stops for other reasons than the size of a number — a decimal's
     * scale — has no such greatest, and a caller that has none passes no {@code Jointly}, so the
     * others are then asked one at a time only.
     */
    private record Jointly(BigInteger greatest) {

        private Jointly {
            if (greatest == null) {
                throw new IllegalArgumentException("a bound the arithmetic stops past is a number");
            }
        }
    }

    /**
     * Whether the terms other than the one at {@code at}, each apart from every other, tied to
     * none and shown to take both ends of its run, come together to a value on each side of every
     * value the one at {@code at} would have to stand at, for an order.
     *
     * <p>The others' weighed sum, the constant with it, takes its least where each takes the end
     * that lessens it and its greatest where each takes the other, and the order is monotone in
     * that sum. So the relation comes out one way at the least sum and the other way at the
     * greatest for every value of the term when it does so at the term's worst value for each:
     * the weighed value that adds most to the least sum still keeps the relation on its first
     * side, and the one that adds least to the greatest sum still keeps it on the other. Only those
     * two rows are witnesses, and they are asked for the ends a term is shown to take and nothing
     * between.
     *
     * <p>A witness is a row that is computed, so every sum along the way has to stay inside the
     * type: the constant and the weighed size of each term at its farthest value, added, are held
     * to the greatest value of the type, which no order of adding passes. That is asked of whole
     * numbers only, where this is all that stops the arithmetic; the values of a term that is not
     * whole are never the ends of a witness.
     */
    private static <P> boolean reachedTogether(List<Term<P>> terms, int at, ExactRatio constant,
                                               Rel relation, boolean[] free, Jointly jointly) {
        if (jointly == null || terms.size() < 3 || constant == null || relation == Rel.EQ
                || relation == Rel.NE) {
            return false;
        }
        Term<P> it = terms.get(at);
        Interval over = wholeRunOf(it.holds(), it.spacing());
        Interval weighedOver = over == null ? null : over.times(it.weight());
        if (weighedOver == null) {
            return false;
        }
        Interval sum = Interval.at(constant);
        ExactRatio size = sizeOf(over, it.weight(), constant.abs());
        for (int i = 0; i < terms.size() && size != null; i++) {
            if (i == at) {
                continue;
            }
            Term<P> each = terms.get(i);
            Interval taken = each.realizes() == null ? null
                    : wholeRunOf(each.realizes(), each.spacing());
            if (!free[i] || taken == null || !each.weight().isWhole()) {
                return false;
            }
            sum = sum.plus(taken.times(each.weight()));
            size = sum == null ? null : sizeOf(taken, each.weight(), size);
        }
        if (size == null || size.compareTo(ExactRatio.of(jointly.greatest())) > 0) {
            return false;
        }
        ExactRatio atLeast = weighedOver.high().plus(sum.low()).orNull();
        ExactRatio atMost = weighedOver.low().plus(sum.high()).orNull();
        if (atLeast == null || atMost == null) {
            return false;
        }
        boolean strictAtLeast = relation == Rel.LT || relation == Rel.GE;
        return (strictAtLeast ? atLeast.signum() < 0 : atLeast.signum() <= 0)
                && (strictAtLeast ? atMost.signum() >= 0 : atMost.signum() > 0);
    }

    /**
     * The whole numbers {@code bounds} is shown to hold, as a run that holds both its ends, so
     * that {@code 1 <= x < 32} and {@code 1 <= x <= 31} are one run — or null where the values
     * are not whole, the run holds none, or an end is none or no number.
     */
    private static Interval wholeRunOf(NumericDomain.Bounds bounds, Granularity spacing) {
        if (spacing != Granularity.DISCRETE) {
            return null;
        }
        WholeRun whole = WholeRun.ofTheValues(bounds);
        if (whole == null || !whole.holdsAWholeNumber() || whole.low == null
                || whole.high == null) {
            return null;
        }
        return new Interval(ExactRatio.of(whole.low), ExactRatio.of(whole.high));
    }

    /** {@code sofar} and the weighed size of {@code run}'s farthest value from nought, or null
     *  where that is no number. */
    private static ExactRatio sizeOf(Interval run, ExactRatio weight, ExactRatio sofar) {
        ExactRatio low = run.low().abs();
        ExactRatio farthest = low.compareTo(run.high().abs()) >= 0 ? low : run.high().abs();
        return farthest.times(weight.abs()).flatMap(sofar::plus).orNull();
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
     * the same end the other reading passes over for two terms held against nought. A difference
     * held apart from one value is the differences below it and the ones above it, two runs, and
     * the relation comes out either way if it does in either run. A
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
        WholeRun middle = WholeRun.reachedFromTheMiddleOf(extent);
        if (middle == null) {
            return Set.of();
        }
        List<WholeRun> left = List.of(middle);
        for (OnTheDifference each : held) {
            left = narrowedBy(left, each);
            if (left == null || left.isEmpty()) {
                return Set.of();
            }
        }
        OnTheDifference line = new OnTheDifference(terms.get(0).weight(), constant, relation);
        if (left.stream().noneMatch(run -> run.comesOut(line, true))
                || left.stream().noneMatch(run -> run.comesOut(line, false))) {
            return Set.of();
        }
        Set<P> out = new LinkedHashSet<>(terms.get(0).madeOf());
        out.addAll(terms.get(1).madeOf());
        return out;
    }

    /**
     * The runs of {@code left} that {@code statement} leaves, or null where it is no run. A
     * difference held apart from one value leaves the differences below it and the ones above it,
     * so the runs it leaves are each run met with either side.
     */
    private static List<WholeRun> narrowedBy(List<WholeRun> left, OnTheDifference statement) {
        List<Rel> sides = statement.relation() == Rel.NE ? List.of(Rel.LT, Rel.GT)
                : List.of(statement.relation());
        List<WholeRun> out = new ArrayList<>();
        for (Rel side : sides) {
            WholeRun where = WholeRun.where(
                    new OnTheDifference(statement.weight(), statement.constant(), side));
            if (where == null) {
                return null;
            }
            for (WholeRun run : left) {
                WholeRun met = run.meet(where);
                if (met.holdsAWholeNumber()) {
                    out.add(met);
                }
            }
        }
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
    private static <P> boolean reaches(List<Term<P>> terms, int by, int of, Interval within,
                                       ExactRatio constant, Rel relation) {
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
        Run needed = needed(terms, by, of, within, constant);
        if (needed == null) {
            return false;
        }
        Spacings spacings = new Spacings(reaching.spacing(), neededSpacing(terms, by, constant));
        // An end of the type moved by a constant or a weight is needed past the end.
        if ((needed.runsDown() || needed.runsUp()) && !itsValue) {
            return false;
        }
        if (exactly) {
            return needed.within(reaching.realizes(), spacings);
        }
        boolean strictlyBelow = strictlyBelow(relation, reaching.weight());
        if ((strictlyBelow ? needed.runsDown() : needed.runsUp())
                && !othersAreTheirPlaces(terms, by)) {
            return false;
        }
        return needed.around(reaching.realizes(), strictlyBelow, spacings);
    }

    /**
     * How the values the term at {@code by} has to stand at are spaced, or null where that is not
     * said.
     *
     * <p>They are what the others come to, over its weight and turned. That is a point of a grid
     * only where the weighing keeps the others' points on one: a weight of one or minus one for
     * the term itself, whole weights for the others, and a constant that is a point of the
     * decimals. The grid is then whole where every other term is whole and the constant is, and
     * the finest decimal grid otherwise. Any other weighing divides or multiplies the step
     * ({@code x / 3} stands at the thirds of a step), so no grid is said, and the run is compared
     * as the numbers it ends at.
     */
    private static <P> Granularity neededSpacing(List<Term<P>> terms, int by,
                                                 ExactRatio constant) {
        boolean keepsTheStep = terms.get(by).weight().abs().equals(ExactRatio.ONE)
                && (constant == null || constant.fitsWrittenDecimal());
        boolean whole = constant == null || constant.isWhole();
        for (int i = 0; i < terms.size() && keepsTheStep; i++) {
            if (i == by) {
                continue;
            }
            Granularity spacing = terms.get(i).spacing();
            keepsTheStep = spacing != null && terms.get(i).weight().isWhole();
            whole &= spacing == Granularity.DISCRETE;
        }
        if (!keepsTheStep) {
            return null;
        }
        return whole ? Granularity.DISCRETE : Granularity.DENSE;
    }

    /**
     * How the values of the reaching term and the values it has to be at are spaced, each null
     * where that is not said, and then the run is compared as the numbers it ends at.
     */
    private record Spacings(Granularity reaching, Granularity needed) {

        /** Neither said: the run is compared as the places it ends at and no more. */
        static final Spacings UNKNOWN = new Spacings(null, null);

        boolean areKnown() {
            return reaching != null && needed != null;
        }
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
    private static <P> Run needed(List<Term<P>> terms, int by, int of, Interval within,
                                  ExactRatio constant) {
        Term<P> reaching = terms.get(by);
        if (within != null && standsAtTheOthersValue(terms, constant)) {
            return within.asRun();
        }
        if (standsAtTheOthersValue(terms, constant)) {
            Term<P> other = terms.get(1 - by);
            Endpoint least = other.holds().min();
            Endpoint greatest = other.holds().max();
            return new OfPlaces(least == null ? null : least.at(),
                    greatest == null ? null : greatest.at(),
                    least != null && !least.inclusive(), greatest != null && !greatest.inclusive());
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
            Interval each = i == of && within != null ? within : Interval.of(terms.get(i).holds());
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

        /** The least end of this run as the number it is, or null where it has none or it is no
         *  number. */
        ExactCut lowerCut();

        /** The greatest end of this run as the number it is, or null where it has none or it is no
         *  number. */
        ExactCut upperCut();

        /** Whether {@code realized} holds every value of this run. */
        default boolean within(NumericDomain.Bounds realized, Spacings spacings) {
            return reaches(realized, Reach.EVERY_VALUE, Reach.EVERY_VALUE, spacings);
        }

        /**
         * Whether {@code realized}, taken by a term spaced as {@code spacings} says, holds beside each value
         * of this run a value strictly below it and one at it or above — or, not
         * {@code strictlyBelow}, one strictly above it and one at it or below.
         */
        default boolean around(NumericDomain.Bounds realized, boolean strictlyBelow,
                               Spacings spacings) {
            return reaches(realized,
                    strictlyBelow ? Reach.STRICTLY_BEYOND : Reach.AT_OR_BEYOND,
                    strictlyBelow ? Reach.AT_OR_BEYOND : Reach.STRICTLY_BEYOND, spacings);
        }

        /** What a value of the run asks of the values a term takes on the side of an end. */
        enum Reach {
            /** The value itself is taken. */
            EVERY_VALUE,
            /** A value strictly short of it is taken. */
            STRICTLY_BEYOND,
            /** The value or one short of it is taken. */
            AT_OR_BEYOND
        }

        /**
         * Whether a term taking {@code realized} takes what {@code atLeast} asks beside the least
         * value of this run and {@code atMost} beside its greatest, for each value of it.
         *
         * <p>Where the spacing of the term and of the values it has to be at are known and every
         * end is a number, this is asked of the points of the grid the values lie on
         * ({@link Lattice}): the least point of this run, and the least point the term takes, and
         * whether one is below the other. That a run leaves an end out, or that two runs stop at one
         * number, then decides nothing by itself. Otherwise only an end the term takes is reached,
         * and one short of the value asked of is not.
         */
        private boolean reaches(NumericDomain.Bounds realized, Reach atLeast, Reach atMost,
                                Spacings spacings) {
            Endpoint least = realized.min();
            Endpoint greatest = realized.max();
            if ((least != null && runsDown()) || (greatest != null && runsUp())) {
                return false;
            }
            if (spacings.areKnown() && onTheGrid(least) && onTheGrid(greatest)) {
                return onTheLattice(realized, atLeast, atMost, spacings);
            }
            return (least == null || lowFrom(least, atLeast))
                    && (greatest == null || highTo(greatest, atMost));
        }

        private static boolean onTheGrid(Endpoint end) {
            return end == null || end.at() instanceof Count;
        }

        private boolean onTheLattice(NumericDomain.Bounds realized, Reach atLeast, Reach atMost,
                                     Spacings spacings) {
            ExactCut start = lowerCut();
            ExactCut stop = upperCut();
            if (spacings.needed() == Granularity.DENSE && spacings.reaching() == Granularity.DISCRETE
                    && atLeast == Reach.EVERY_VALUE && !isOneWholeValue(start, stop)) {
                return false;
            }
            return (realized.min() == null
                    || (start != null && reachesFrom(atLeast, start, cutOf(realized.min()), spacings)))
                    && (realized.max() == null
                    || (stop != null && reachesTo(atMost, stop, cutOf(realized.max()), spacings)));
        }

        /** Whether the run is the one value, and a whole number: all the whole term can be at. */
        private static boolean isOneWholeValue(ExactCut start, ExactCut stop) {
            return start != null && stop != null && start.inclusive() && stop.inclusive()
                    && start.at().compareTo(stop.at()) == 0 && start.at().isWhole();
        }

        private static ExactCut cutOf(Endpoint end) {
            return new ExactCut(((Count) end.at()).exactly(), end.inclusive());
        }

        /** Whether the term, taking points from {@code taken}, has beside the least point of
         *  this run, at {@code start}, what {@code reach} asks. */
        private static boolean reachesFrom(Reach reach, ExactCut start, ExactCut taken,
                                           Spacings spacings) {
            Lattice.Point asked = Lattice.least(spacings.needed(), start);
            Lattice.Point takes = Lattice.least(
                    reach == Reach.EVERY_VALUE ? spacings.needed() : spacings.reaching(), taken);
            if (asked == null || takes == null) {
                return false;
            }
            Integer order = Lattice.compare(takes, asked);
            return order != null && (reach == Reach.STRICTLY_BEYOND ? order < 0 : order <= 0);
        }

        /** The same beside the greatest point of this run, at {@code stop}. */
        private static boolean reachesTo(Reach reach, ExactCut stop, ExactCut taken,
                                         Spacings spacings) {
            Lattice.Point asked = Lattice.greatest(spacings.needed(), stop);
            Lattice.Point takes = Lattice.greatest(
                    reach == Reach.EVERY_VALUE ? spacings.needed() : spacings.reaching(), taken);
            if (asked == null || takes == null) {
                return false;
            }
            Integer order = Lattice.compare(takes, asked);
            return order != null && (reach == Reach.STRICTLY_BEYOND ? order > 0 : order >= 0);
        }

        /** An end of the term below the least value asked of is reached, and one at it only where
         *  the term takes it and the value asked of is not short of it. */
        private boolean lowFrom(Endpoint end, Reach reach) {
            Integer order = againstTheLeast(end.at());
            return order != null && (order < 0
                    || (order == 0 && reach != Reach.STRICTLY_BEYOND && end.inclusive()));
        }

        private boolean highTo(Endpoint end, Reach reach) {
            Integer order = againstTheGreatest(end.at());
            return order != null && (order > 0
                    || (order == 0 && reach != Reach.STRICTLY_BEYOND && end.inclusive()));
        }
    }

    /** A run of values of any type, between two of them, each end open where the run leaves out
     *  the value it stops at. */
    private record OfPlaces(Place min, Place max, boolean openBelow, boolean openAbove)
            implements Run {

        @Override
        public ExactCut lowerCut() {
            return min instanceof Count count ? new ExactCut(count.exactly(), !openBelow) : null;
        }

        @Override
        public ExactCut upperCut() {
            return max instanceof Count count ? new ExactCut(count.exactly(), !openAbove) : null;
        }

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
    private record OfNumbers(ExactRatio min, ExactRatio max, boolean openBelow, boolean openAbove)
            implements Run {

        OfNumbers(ExactRatio min, ExactRatio max) {
            this(min, max, false, false);
        }

        @Override
        public ExactCut lowerCut() {
            return min == null ? null : new ExactCut(min, !openBelow);
        }

        @Override
        public ExactCut upperCut() {
            return max == null ? null : new ExactCut(max, !openAbove);
        }

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

    /**
     * A run of numbers, null at an end where nothing bounds it, and each end saying whether the
     * number it stops at is one of the run.
     */
    private record Interval(ExactCut lower, ExactCut upper) {

        /** A run with both ends inclusive. */
        Interval(ExactRatio low, ExactRatio high) {
            this(low == null ? null : ExactCut.inclusive(low),
                    high == null ? null : ExactCut.inclusive(high));
        }

        static Interval at(ExactRatio value) {
            return new Interval(value, value);
        }

        /** The run {@code bounds} gives, or null where an end is no number. */
        static Interval of(NumericDomain.Bounds bounds) {
            ExactCut low = cut(bounds.min());
            ExactCut high = cut(bounds.max());
            if ((bounds.min() != null && low == null) || (bounds.max() != null && high == null)) {
                return null;
            }
            return new Interval(low, high);
        }

        private static ExactCut cut(Endpoint end) {
            return end != null && end.at() instanceof Count count
                    ? new ExactCut(count.exactly(), end.inclusive()) : null;
        }

        ExactRatio low() {
            return lower == null ? null : lower.at();
        }

        ExactRatio high() {
            return upper == null ? null : upper.at();
        }

        /** The run of the sums of a value of this and a value of {@code other}, or null where an
         *  end is no number — or {@code other} is none, which is what a product that held no
         *  number is. */
        Interval plus(Interval other) {
            if (other == null) {
                return null;
            }
            ExactCut least = lower == null || other.lower == null ? null
                    : ExactCut.meetingBoth(lower, other.lower).orNull();
            ExactCut most = upper == null || other.upper == null ? null
                    : ExactCut.meetingBoth(upper, other.upper).orNull();
            if ((lower != null && other.lower != null && least == null)
                    || (upper != null && other.upper != null && most == null)) {
                return null;
            }
            return new Interval(least, most);
        }

        Interval times(ExactRatio by) {
            ExactCut one = lower == null ? null : scaled(lower, by);
            ExactCut two = upper == null ? null : scaled(upper, by);
            if ((lower != null && one == null) || (upper != null && two == null)) {
                return null;
            }
            return by.signum() >= 0 ? new Interval(one, two) : new Interval(two, one);
        }

        private static ExactCut scaled(ExactCut cut, ExactRatio by) {
            ExactRatio at = cut.at().times(by).orNull();
            return at == null ? null : new ExactCut(at, cut.inclusive());
        }

        Run asRun() {
            return new OfNumbers(low(), high(), lower != null && !lower.inclusive(),
                    upper != null && !upper.inclusive());
        }
    }

    /**
     * A run of numbers as cuts, empty where its ends have crossed. It is what a dense term's
     * values are worked out as: a run ends open or closed, and a difference of two such runs is
     * runs again.
     *
     * <p>The ends are exact numbers and the values are the decimals, the points of a grid a step
     * apart ({@link Lattice}). Whether a run holds a value is where the grid's points fall in it:
     * a run open at both ends of a number and the next point holds none, and one a third wide holds
     * none where its ends are one number no decimal is.
     */
    private record Span(ExactCut lower, ExactCut upper) {

        /** The run {@code bounds} gives, or null where an end is no number. */
        static Span ofTheValues(NumericDomain.Bounds bounds) {
            Interval run = Interval.of(bounds);
            return run == null ? null : new Span(run.lower(), run.upper());
        }

        /** The values {@code statement} holds at, or null where they are no run. */
        static Span where(OnTheDifference statement) {
            ExactRatio at = statement.constant().negated().dividedBy(statement.weight()).orNull();
            if (at == null) {
                return null;
            }
            Rel relation = statement.weight().signum() < 0 ? statement.relation().turned()
                    : statement.relation();
            return switch (relation) {
                case LT -> new Span(null, ExactCut.exclusive(at));
                case LE -> new Span(null, ExactCut.inclusive(at));
                case GT -> new Span(ExactCut.exclusive(at), null);
                case GE -> new Span(ExactCut.inclusive(at), null);
                case EQ -> new Span(ExactCut.inclusive(at), ExactCut.inclusive(at));
                case NE -> null;
            };
        }

        Span meet(Span other) {
            return new Span(ExactCut.tighterLower(lower, other.lower),
                    ExactCut.tighterUpper(upper, other.upper));
        }

        /** Whether a decimal lies in a run: it does, it does not, or that is not worked out. */
        enum Occupancy { HOLDS, EMPTY, UNKNOWN }

        /**
         * Whether a decimal lies in this run: the least one in it is not past the greatest. Both
         * are points of the grid even where an end is no decimal, and where the ends are too close
         * for the places they are moved from to say which is first, it is not worked out, which
         * nothing reads as either answer.
         */
        Occupancy occupancy() {
            if (lower == null || upper == null) {
                return Occupancy.HOLDS;
            }
            int order = lower.at().compareTo(upper.at());
            if (order > 0) {
                return Occupancy.EMPTY;
            }
            if (order == 0) {
                return lower.inclusive() && upper.inclusive()
                        && Lattice.holds(Granularity.DENSE, lower.at())
                        ? Occupancy.HOLDS : Occupancy.EMPTY;
            }
            Integer placed = Lattice.compare(Lattice.least(Granularity.DENSE, lower),
                    Lattice.greatest(Granularity.DENSE, upper));
            if (placed == null) {
                return Occupancy.UNKNOWN;
            }
            return placed > 0 ? Occupancy.EMPTY : Occupancy.HOLDS;
        }

        /**
         * What is left of this run with {@code taken} out of it: up to two runs, or null where
         * whether one of them holds a decimal is not worked out.
         */
        List<Span> without(Span taken) {
            List<Span> out = new ArrayList<>();
            if (taken.lower != null) {
                Span below = meet(new Span(null, new ExactCut(taken.lower.at(),
                        !taken.lower.inclusive())));
                switch (below.occupancy()) {
                    case HOLDS -> out.add(below);
                    case UNKNOWN -> {
                        return null;
                    }
                    case EMPTY -> { }
                }
            }
            if (taken.upper != null) {
                Span above = meet(new Span(new ExactCut(taken.upper.at(),
                        !taken.upper.inclusive()), null));
                switch (above.occupancy()) {
                    case HOLDS -> out.add(above);
                    case UNKNOWN -> {
                        return null;
                    }
                    case EMPTY -> { }
                }
            }
            return out;
        }
    }
}
