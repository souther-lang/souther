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
import java.util.TreeSet;
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
     *                 An end the run holds is one it takes. One it leaves out is, where its values
     *                 are dense, one some value it takes is as near as any other value asked of:
     *                 so a value beyond an end is one it takes, and an end that is not taken
     *                 matters only where it is the value asked of
     * @param takes    what values it takes, compared with another term's by equality — null where
     *                 nothing says
     * @param itsPlace whether it is the value at its one place, so that an end of its type it runs
     *                 to is one value there and not every value something answers it at
     * @param spacing  how its values are spaced, or null where that is not said. Only a dense term
     *                 takes values as near as asked of an end its run leaves out
     * @param runsTo   where the order its values are counted on stops, open on a side it has no
     *                 end — null where nothing says. A run of the term open on a side is open
     *                 only as far as this: an {@code Int} runs on past the last date, and a
     *                 decimal runs on without end. An end {@code realizes} has is a value this
     *                 holds, since a value is taken only on the order it is counted on; a side it
     *                 leaves open is read as though the order ran on, and a witness asked there
     *                 stays inside this ({@link Run#passes})
     */
    public record Term<P>(List<P> madeOf, ExactRatio weight, NumericDomain.Bounds holds,
                          NumericDomain.Bounds realizes, Object takes, boolean itsPlace,
                          Granularity spacing, NumericDomain.Bounds runsTo) {

        public Term {
            if (madeOf == null || weight == null || weight.signum() == 0 || holds == null) {
                throw new IllegalArgumentException("a term of a relation is made of something,"
                        + " weighed by something other than nought and held somewhere");
            }
            Interval taken = realizes == null || runsTo == null ? null : Interval.of(realizes);
            Interval order = taken == null ? null : Interval.of(runsTo);
            if (order != null && (pastTheEnd(taken.upper(), order.upper(), spacing, true)
                    || pastTheEnd(taken.lower(), order.lower(), spacing, false))) {
                throw new IllegalArgumentException("a value is taken only on the order it is"
                        + " counted on: " + realizes + " past " + runsTo);
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
     * @param greatest    the greatest value the type the form is worked out in holds, or null
     *                    where it holds no greatest: a row passing it is no witness
     */
    public static <P> Set<P> of(List<Term<P>> terms, ExactRatio constant, Rel relation,
                                BiPredicate<P, P> overlap, Independence independent,
                                BigInteger greatest) {
        Set<P> out = new LinkedHashSet<>();
        for (int at = 0; at < terms.size(); at++) {
            if (reachedBySome(terms, at, constant, relation, overlap, independent, null,
                    Arithmetic.upTo(greatest))) {
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
         * @param ofTheTypeAlone those of {@link #lines()} drawn only because the orders the terms
         *                 are counted on stop: worked out with every term free to run past where
         *                 its type stops, the relation draws none of them. {@code count >= k}
         *                 holds whatever {@code k} is at the greatest count only because no
         *                 {@code k} is greater. Such a line is no class of the model's
         */
        record Settled(List<SettledRun> runs, ExactCut least, ExactCut greatest, boolean whole,
                       List<Line> ofTheTypeAlone)
                implements Leaves {

            /** Runs of a term whose values are whole, its ends being the whole numbers it holds. */
            public static Settled ofWhole(List<SettledRun> runs, BigInteger least,
                                          BigInteger greatest) {
                return new Settled(runs, least == null ? null : wholeEnd(least),
                        greatest == null ? null : wholeEnd(greatest), true, List.of());
            }

            public Settled {
                runs = List.copyOf(runs);
                ofTheTypeAlone = List.copyOf(ofTheTypeAlone);
                if (runs.isEmpty()) {
                    throw new IllegalArgumentException("a term some values of which settle a"
                            + " relation has some");
                }
            }

            /** The same runs, those of their lines {@code model} does not draw drawn by the
             *  orders' ends alone. */
            Settled besideWhatTheModelDraws(List<Line> model) {
                return new Settled(runs, least, greatest, whole,
                        lines().stream().filter(each -> !model.contains(each)).toList());
            }

            /** The lines the model draws: {@link #lines()} but those the orders' ends alone do. */
            public List<Line> linesOfTheModel() {
                return lines().stream().filter(each -> !ofTheTypeAlone.contains(each)).toList();
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
        return leavesOf(terms, at, constant, relation, overlap, independent, granularity,
                greatest, List.of());
    }

    /**
     * The same, with {@code supports}: sets of terms read off one value, whose joint values are
     * given and not taken from the terms one by one. They show a term undivided where the others
     * could not, and say nothing of the values that settle it.
     */
    public static <P> Leaves leavesOf(List<Term<P>> terms, int at, ExactRatio constant,
                                      Rel relation, BiPredicate<P, P> overlap,
                                      Independence independent, Granularity granularity,
                                      BigInteger greatest, List<JointSupport> supports) {
        return leavesOf(terms, at, constant, Asking.of(relation), overlap, independent,
                granularity, greatest, supports);
    }

    /**
     * The same, of a relation asked only where the form is not nought: the rows reaching it are
     * kept off its line, as a way that took {@code a != b} before {@code a < b} keeps them.
     *
     * <p>A row then comes out true where the form is strictly on the relation's side and false
     * where it is strictly on the other. So a value of the term settles the relation true where no
     * other value of the form is strictly on the other side, and false where none is strictly on
     * its side; and a value is left either way where the form reaches both sides strictly, which
     * is the relation and the one beside it that takes the line in or leaves it out both leaving
     * the value undivided. A value at which the others leave the form only nought has no row, and
     * nothing is shown.
     *
     * @param relation an order: an equality kept off its own line holds nothing
     */
    public static <P> Leaves leavesOffItsLine(List<Term<P>> terms, int at, ExactRatio constant,
                                              Rel relation, BiPredicate<P, P> overlap,
                                              Independence independent, Granularity granularity,
                                              BigInteger greatest, List<JointSupport> supports) {
        if (relation == Rel.EQ || relation == Rel.NE) {
            return null;
        }
        return leavesOf(terms, at, constant, Asking.offItsLine(relation), overlap, independent,
                granularity, greatest, supports);
    }

    /**
     * What the values of a term are asked: the statement of the form every other value meets
     * where a value settles the relation true, the one where it settles it false, and the
     * relations a value left by neither has to be left either way by.
     *
     * @param apart whether a value both settling statements hold at is one no row reaches, rather
     *              than one that cannot occur
     */
    private record Asking(Rel holding, Rel failing, List<Rel> leftBy, boolean apart) {

        /** The relation as it stands. */
        static Asking of(Rel relation) {
            return new Asking(relation, relation.denied(), List.of(relation), false);
        }

        /** The order {@code relation}, its line kept out. */
        static Asking offItsLine(Rel relation) {
            return new Asking(takingTheLine(relation), takingTheLine(relation.denied()),
                    List.of(relation, relation == takingTheLine(relation)
                            ? leavingTheLine(relation) : takingTheLine(relation)), true);
        }

        private static Rel takingTheLine(Rel order) {
            return switch (order) {
                case LT -> Rel.LE;
                case GT -> Rel.GE;
                default -> order;
            };
        }

        private static Rel leavingTheLine(Rel order) {
            return switch (order) {
                case LE -> Rel.LT;
                case GE -> Rel.GT;
                default -> order;
            };
        }
    }

    private static <P> Leaves leavesOf(List<Term<P>> terms, int at, ExactRatio constant,
                                       Asking asking, BiPredicate<P, P> overlap,
                                       Independence independent, Granularity granularity,
                                       BigInteger greatest, List<JointSupport> supports) {
        Arithmetic arithmetic = Arithmetic.upTo(greatest);
        Jointly jointly = granularity == Granularity.DISCRETE && arithmetic.stopsAtASize()
                ? new Jointly(arithmetic) : null;
        if (asking.leftBy().stream().allMatch(relation ->
                reachedBySome(terms, at, constant, relation, overlap, independent, jointly,
                        arithmetic)
                        || reachedAcrossGroups(terms, at, constant, relation, overlap,
                                independent, supports, jointly))) {
            return new Leaves.Undivided();
        }
        if (granularity == Granularity.DENSE) {
            return leavesOfADenseTerm(terms, at, constant, asking, overlap, independent);
        }
        Settling free = settlingOf(terms, at, constant, asking, granularity, arithmetic);
        Leaves shownFree = shown(free, terms, at, constant, asking, overlap, independent,
                jointly, arithmetic);
        if (free == null) {
            return shownFree;
        }
        // Asked again of the values each term takes in a row that is computed, a value of the term
        // may settle the relation that the free terms left either way: no greater value of the
        // other is there to fail it. That is a line of the orders' ends and the arithmetic's, and
        // none of the model's. The model's lines are those the free terms' settling runs draw,
        // whether or not the values between them were shown reached: that is a second question,
        // and one those ends may be all that kept from being shown.
        List<Term<P>> withinTheirOrders = withinTheRowsThatCompute(terms.stream()
                .map(term -> withinItsOrder(term, arithmetic)).toList(), constant, arithmetic);
        Settling bounded = withinTheirOrders.equals(terms) ? null
                : settlingOf(withinTheirOrders, at, constant, asking, granularity, arithmetic);
        List<Line> model = free.lines();
        // Shown already, and drawing no line the free runs do not: nothing is left to ask.
        if (bounded == null || (shownFree != null && model.containsAll(bounded.lines()))) {
            return shownFree;
        }
        return shown(bounded, withinTheirOrders, at, constant, asking, overlap, independent,
                jointly, arithmetic) instanceof Leaves.Settled settled
                ? settled.besideWhatTheModelDraws(model) : shownFree;
    }

    /**
     * {@code term}, holding only the whole values it takes in a row that is computed: the values
     * it holds, cut where the order it is counted on stops and where its value weighed passes
     * {@code arithmetic} ({@link Arithmetic}). {@code a >= 100 * b} has no false row at an
     * {@code a} within a hundred of the greatest {@code Int}, since a {@code b} past it weighed
     * passes the type, and that value is settled by the arithmetic alone. A term whose values are
     * no whole numbers is left as it is.
     */
    private static <P> Term<P> withinItsOrder(Term<P> term, Arithmetic arithmetic) {
        if (term.spacing() != Granularity.DISCRETE || !endsAtNumbers(term.holds())) {
            return term;
        }
        NumericDomain.Bounds cut = term.holds();
        if (endsAtNumbers(term.runsTo())) {
            cut = cut.meet(term.runsTo());
        }
        BigInteger weighed = arithmetic.stopsAtASize()
                ? ExactRatio.of(arithmetic.greatest()).dividedBy(term.weight().abs())
                        .flatMap(ExactRatio::floor).orNull()
                : null;
        if (weighed != null) {
            cut = cut.meet(new NumericDomain.Bounds(
                    Endpoint.inclusive(Count.of(new BigDecimal(weighed.negate()))),
                    Endpoint.inclusive(Count.of(new BigDecimal(weighed)))));
        }
        if (cut.equals(term.holds()) || !cut.holdsAValue()) {
            return term;
        }
        return new Term<>(term.madeOf(), term.weight(), cut, term.realizes(), term.takes(),
                term.itsPlace(), term.spacing(), term.runsTo());
    }

    /**
     * {@code terms}, each holding only the values it takes in a row that computes
     * ({@link Arithmetic}). The positive addends of a row come to the greatest {@code Int} at
     * most, and so do the negative ones, so a term weighed cannot pass what the greatest leaves
     * once the others and the constant are at their least on that side: in
     * {@code a + b - s - 150000 >= 0}, {@code s + 150000} computes only for an {@code s} of the
     * greatest less 150000, and an {@code a} at the greatest has no false row.
     */
    private static <P> List<Term<P>> withinTheRowsThatCompute(List<Term<P>> terms,
                                                              ExactRatio constant,
                                                              Arithmetic arithmetic) {
        if (!arithmetic.stopsAtASize() || constant == null) {
            return terms;
        }
        // What each term weighed comes to at least on each side of nought, and the sum of those and
        // the constant's, so that what the others come to is the sum less the term's own. A term
        // whose values are no run of numbers leaves every other term uncut, and is itself cut by
        // what the rest come to.
        int size = terms.size();
        ExactRatio[] leastPositive = new ExactRatio[size];
        ExactRatio[] leastNegative = new ExactRatio[size];
        ExactRatio totalPositive = constant.signum() > 0 ? constant : ExactRatio.ZERO;
        ExactRatio totalNegative = constant.signum() < 0 ? constant.negated() : ExactRatio.ZERO;
        int unread = -1;
        int unreadCount = 0;
        for (int j = 0; j < size && totalPositive != null && totalNegative != null; j++) {
            Interval holds = Interval.of(terms.get(j).holds());
            Interval weighed = holds == null ? null : holds.times(terms.get(j).weight());
            if (weighed == null) {
                unread = j;
                unreadCount++;
                continue;
            }
            leastPositive[j] = weighed.low() != null && weighed.low().signum() > 0
                    ? weighed.low() : ExactRatio.ZERO;
            leastNegative[j] = weighed.high() != null && weighed.high().signum() < 0
                    ? weighed.high().negated() : ExactRatio.ZERO;
            totalPositive = totalPositive.plus(leastPositive[j]).orNull();
            totalNegative = totalNegative == null ? null
                    : totalNegative.plus(leastNegative[j]).orNull();
        }
        if (unreadCount > 1 || totalPositive == null || totalNegative == null) {
            return terms;
        }
        ExactRatio greatest = ExactRatio.of(arithmetic.greatest());
        List<Term<P>> cut = new ArrayList<>(terms);
        for (int i = 0; i < size; i++) {
            Term<P> term = terms.get(i);
            if ((unreadCount == 1 && unread != i) || term.spacing() != Granularity.DISCRETE
                    || !endsAtNumbers(term.holds())) {
                continue;
            }
            ExactRatio positive = unreadCount == 1 ? totalPositive
                    : totalPositive.minus(leastPositive[i]).orNull();
            ExactRatio negative = unreadCount == 1 ? totalNegative
                    : totalNegative.minus(leastNegative[i]).orNull();
            if (positive == null || negative == null) {
                continue;
            }
            ExactRatio most = greatest.minus(positive).orNull();
            ExactRatio least = greatest.minus(negative).orNull();
            ExactRatio high = most == null ? null : most.dividedBy(term.weight()).orNull();
            ExactRatio low = least == null ? null
                    : least.negated().dividedBy(term.weight()).orNull();
            if (high == null || low == null) {
                continue;
            }
            ExactRatio from = term.weight().signum() > 0 ? low : high;
            ExactRatio to = term.weight().signum() > 0 ? high : low;
            BigInteger lowest = from.ceiling().orNull();
            BigInteger highest = to.floor().orNull();
            if (lowest == null || highest == null) {
                continue;
            }
            NumericDomain.Bounds held = term.holds().meet(new NumericDomain.Bounds(
                    Endpoint.inclusive(Count.of(new BigDecimal(lowest))),
                    Endpoint.inclusive(Count.of(new BigDecimal(highest)))));
            if (!held.equals(term.holds()) && held.holdsAValue()) {
                cut.set(i, new Term<>(term.madeOf(), term.weight(), held, term.realizes(),
                        term.takes(), term.itsPlace(), term.spacing(), term.runsTo()));
            }
        }
        return cut;
    }

    /** Whether {@code bounds} is there and each end it has is a number. */
    private static boolean endsAtNumbers(NumericDomain.Bounds bounds) {
        return bounds != null && (bounds.min() == null || bounds.min().at() instanceof Count)
                && (bounds.max() == null || bounds.max().at() instanceof Count);
    }

    /**
     * Where the values of a whole-numbered term stand to a relation, before anything is shown of
     * the values left between: the runs that settle it whatever the others are, every one with a
     * row that computes, the values the term holds, and those left between the runs — null where
     * they are two runs and not one.
     */
    private record Settling(List<SettledRun> runs, WholeRun held, WholeRun between) {

        /** The lines the runs part the term's values at; none where no run settles it. */
        List<Line> lines() {
            return runs.isEmpty() ? List.of()
                    : Leaves.Settled.ofWhole(inOrder(runs, true), held.low, held.high).lines();
        }
    }

    /**
     * Which values of the whole-numbered term at {@code at} settle the relation whatever the
     * others are — none being an answer — or null where that is not worked out: a term with no
     * whole values, others no run of numbers, a value no row computes, or one settling it both
     * ways where that cannot be.
     */
    private static <P> Settling settlingOf(List<Term<P>> terms, int at, ExactRatio constant,
                                           Asking asking, Granularity granularity,
                                           Arithmetic arithmetic) {
        Term<P> it = terms.get(at);
        if (granularity != Granularity.DISCRETE || constant == null) {
            return null;
        }
        WholeRun held = WholeRun.ofTheValues(it.holds());
        Interval rest = restOf(terms, at, constant);
        if (held == null || rest == null) {
            return null;
        }
        List<SettledRun> runs = new ArrayList<>();
        List<WholeRun> settledTrue = new ArrayList<>();
        WholeRun between = held;
        for (boolean holds : List.of(true, false)) {
            Rel asked = holds ? asking.holding() : asking.failing();
            for (OnTheDifference statement : settledBy(it.weight(), rest, asked)) {
                WholeRun settling = WholeRun.where(statement);
                if (settling == null || !settling.holdsAWholeNumber()) {
                    continue;
                }
                between = between == null ? null : between.without(settling);
                WholeRun here = settling.meet(held);
                if (here.holdsAWholeNumber()) {
                    if (asking.apart() && !holds && settledTrue.stream()
                            .anyMatch(one -> one.meet(here).holdsAWholeNumber())) {
                        return null;
                    }
                    if (holds) {
                        settledTrue.add(here);
                    }
                    runs.add(SettledRun.whole(here.low, here.high, holds));
                }
            }
        }
        // Each run's row: the run's value nearest nought, each other number at its own, weighed.
        ExactRatio[] row = new ExactRatio[terms.size() + 1];
        row[terms.size()] = constant;
        for (int i = 0; i < terms.size(); i++) {
            row[i] = i == at ? null : weighedAt(nearestValue(Interval.of(terms.get(i).holds())),
                    terms.get(i).weight());
        }
        for (SettledRun each : runs) {
            row[at] = weighedAt(nearestValue(new Interval(each.from(), each.to())), it.weight());
            if (!arithmetic.computes(row)) {
                return null;
            }
        }
        return new Settling(runs, held, between);
    }

    /**
     * {@code settling} as the term's values are left, where every value between its runs is
     * shown left either way — or null where it is not, where no run settles it, or where the
     * values between are two runs.
     */
    private static <P> Leaves shown(Settling settling, List<Term<P>> terms, int at,
                                    ExactRatio constant, Asking asking,
                                    BiPredicate<P, P> overlap, Independence independent,
                                    Jointly jointly, Arithmetic arithmetic) {
        if (settling == null || settling.runs().isEmpty() || settling.between() == null) {
            return null;
        }
        Term<P> it = terms.get(at);
        WholeRun between = settling.between();
        if (between.holdsAWholeNumber()) {
            List<Term<P>> narrowed = new ArrayList<>(terms);
            narrowed.set(at, new Term<>(it.madeOf(), it.weight(), between.asBounds(),
                    it.realizes(), it.takes(), it.itsPlace(), it.spacing(), it.runsTo()));
            if (!asking.leftBy().stream().allMatch(relation -> reachedBySome(narrowed, at,
                    constant, relation, overlap, independent, jointly, arithmetic))) {
                return null;
            }
        }
        return Leaves.Settled.ofWhole(inOrder(settling.runs(), true), settling.held().low,
                settling.held().high);
    }

    /** What the terms but the one at {@code at} and {@code constant} come to together, wherever
     *  they lie; null where one of them is no run of numbers. */
    private static <P> Interval restOf(List<Term<P>> terms, int at, ExactRatio constant) {
        Interval rest = Interval.at(constant);
        for (int i = 0; i < terms.size() && rest != null; i++) {
            if (i != at) {
                Interval each = Interval.of(terms.get(i).holds());
                Interval weighed = each == null ? null : each.times(terms.get(i).weight());
                rest = weighed == null ? null : rest.plus(weighed);
            }
        }
        return rest;
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
        Arithmetic arithmetic = Arithmetic.upTo(greatest);
        // The product a partner reaching over a value comes to lies within twice the level.
        if (!arithmetic.computes(level.abs(), level.abs())) {
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
                    && reachesOverAFactor(other, between, sign, level, relation))) {
                return null;
            }
        }
        ExactRatio nearOther = nearestValue(lies);
        for (SettledRun each : runs) {
            // The least product of the run's: each factor at its value nearest nought.
            ExactRatio near = nearestValue(new Interval(each.from(), each.to()));
            if (!arithmetic.computes(near == null || nearOther == null ? null
                    : weighedAt(near, nearOther))) {
                return null;
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

    /**
     * That one term of a relation lies, at each value of another, at every whole number from
     * {@code least} to that value less {@code belowTheWhole} and at no other — and takes each of
     * them in some row beside that value: where a walk over every element hands its step stands
     * beside how many the walk is over, from nought to one below.
     *
     * <p>The two are read off one container, so neither is apart from the other, and what one
     * takes is not asked of it alone. A value of the whole at which the part lies nowhere — a
     * container of none, which hands the step nothing — is one no row reaches the relation at.
     *
     * @param part          the index of the term that lies within the other
     * @param whole         the index of the term it lies within
     * @param least         the least value the part takes
     * @param belowTheWhole how far below the whole's value the greatest value the part takes is
     */
    public record WithinTheWhole(int part, int whole, BigInteger least,
                                 BigInteger belowTheWhole) {

        public WithinTheWhole {
            if (part == whole || part < 0 || whole < 0 || least == null
                    || belowTheWhole == null) {
                throw new IllegalArgumentException("a part lies within another term, between a"
                        + " number and the other's value less a number: " + part + " in "
                        + whole);
            }
        }
    }

    /**
     * What a relation of a whole and a part lying within it ({@link WithinTheWhole}) leaves the
     * values of the whole — or null where nothing is shown.
     *
     * <p>Fixing a value of the whole leaves the relation a run of the part, every value of which
     * is taken there. Weighed by one either way, the part makes the form every whole number
     * between two ends, and each end is the whole's value weighed and moved, so the whole's values
     * at which every value of the form meets the relation, or none does, are where a statement of
     * one form of the whole holds: those settle it, and at each other value the form reaches both
     * sides. So nothing past what the two terms are is asked, and the relation is read only where
     * they are all its terms.
     *
     * <p>Only at values of the whole every one of which some row takes, and at which the part lies
     * somewhere.
     *
     * <p>And only of rows that compute. What is said of a value of the whole is said of every value
     * of the part there, so every one of those rows is asked, and not one standing for them. The
     * positive addends of a row, and the negative ones, come to a sum that is a straight function of
     * the part at one value of the whole, so the rows at the part's two ends computing is every row
     * there computing. And from the least value of the whole on, no addend shrinks as the whole
     * grows, so the values whose rows all compute are a run from the least up, found by halving
     * ({@link #computedUpTo}). Past them a row is evaluated at the part's values in order and stops
     * at the first whose addends pass the greatest, so it compares the part from its least to an
     * end that is a straight function of the whole — the greatest less what the whole and the
     * constant add on the part's side — and the relation is read there over those values. Past the
     * values where even the part's least does not compute, no row reaches it, and nothing is said
     * there ({@link #reachedUpTo}). So the answer is of the values some row reaches the relation
     * at, every one of them; a line it draws that the model's own reading does not is the
     * arithmetic's ({@link Leaves.Settled#ofTheTypeAlone}).
     *
     * @param greatest the greatest value the type the form is worked out in holds, or null where it
     *                 holds no greatest
     */
    public static <P> Leaves leavesOfTheWhole(List<Term<P>> terms, WithinTheWhole within,
                                              ExactRatio constant, Rel relation,
                                              BigInteger greatest) {
        if (terms.size() != 2 || within.part() >= 2 || within.whole() >= 2 || constant == null
                || !constant.isWhole()) {
            return null;
        }
        Term<P> part = terms.get(within.part());
        Term<P> whole = terms.get(within.whole());
        BigInteger weight = whole.weight().isWhole() ? whole.weight().floor().orNull() : null;
        BigInteger offset = constant.floor().orNull();
        if (weight == null || offset == null || whole.spacing() != Granularity.DISCRETE
                || whole.realizes() == null || part.weight().abs().compareTo(ExactRatio.ONE) != 0) {
            return null;
        }
        WholeRun held = WholeRun.ofTheValues(whole.holds());
        WholeRun taken = WholeRun.ofTheValues(whole.realizes());
        if (held == null || taken == null) {
            return null;
        }
        WholeRun values = held.meet(new WholeRun(within.least().add(within.belowTheWhole()), null));
        if (!values.holdsAWholeNumber() || !taken.covers(values) || values.low == null
                || within.least().signum() < 0 || within.belowTheWhole().signum() < 0) {
            return null;
        }
        Arithmetic arithmetic = Arithmetic.upTo(greatest);
        if (!rowsComputeAt(values.low, within, whole.weight(), part.weight(), constant,
                arithmetic)) {
            return null;
        }
        BigInteger computed = computedUpTo(values, within, whole.weight(), part.weight(),
                constant, arithmetic);
        Form form = new Form(part.weight().signum() > 0, weight, offset, within.least());
        // The model's own reading: the part at every value from its least to the whole's value
        // less how far below, whatever the arithmetic does.
        BigInteger below = within.belowTheWhole();
        List<SettledRun> free = settledWithin(values, relation,
                form.upTo(BigInteger.ONE, below.negate()));
        if (computed == null || (values.high != null && computed.compareTo(values.high) >= 0)) {
            return free.isEmpty() ? new Leaves.Undivided()
                    : Leaves.Settled.ofWhole(free, values.low, values.high);
        }
        // Past the values whose every row computes, a row computes at the part's values from its
        // least up to where the addends on the part's side pass the greatest — a run of them that
        // shrinks as the whole grows — and stops at the first that does not, those before it read.
        // Past the values where even the least computes, no row reaches the relation at all.
        BigInteger reached = reachedUpTo(values, computed, within, whole.weight(), part.weight(),
                constant, arithmetic);
        WholeRun all = new WholeRun(values.low, computed);
        List<SettledRun> runs = new ArrayList<>(settledWithin(all, relation,
                form.upTo(BigInteger.ONE, below.negate())));
        if (reached.compareTo(computed) > 0) {
            runs = joined(runs, settledWithin(new WholeRun(computed.add(BigInteger.ONE), reached),
                    relation, form.upTo(form.sameSideSlope().negate(),
                            arithmetic.greatest().subtract(form.sameSideOffset()))));
        }
        if (runs.isEmpty()) {
            return new Leaves.Undivided();
        }
        List<Line> model = free.isEmpty() ? List.of()
                : Leaves.Settled.ofWhole(free, values.low, values.high).lines();
        return Leaves.Settled.ofWhole(runs, values.low, reached).besideWhatTheModelDraws(model);
    }

    /**
     * A form of a whole weighed by {@code weight}, a part weighed by one, up where {@code up},
     * and {@code offset}, the part taking every whole number from {@code least} to an upper end
     * that is a straight function of the whole.
     */
    private record Form(boolean up, BigInteger weight, BigInteger offset, BigInteger least) {

        /** The ends of the form at a value v of the whole, the part's upper end being
         *  {@code slope}·v + {@code by}: the part at its least, and at that end. */
        Lines upTo(BigInteger slope, BigInteger by) {
            return up
                    ? new Lines(weight, offset.add(least), weight.add(slope), offset.add(by))
                    : new Lines(weight.subtract(slope), offset.subtract(by), weight,
                            offset.subtract(least));
        }

        /** How much of the whole's addend grows on the part's side of nought for each value: all
         *  of it where the two have one sign, and none where they have two. */
        BigInteger sameSideSlope() {
            return weight.signum() == (up ? 1 : -1) ? weight.abs() : BigInteger.ZERO;
        }

        /** And of the constant's. */
        BigInteger sameSideOffset() {
            return offset.signum() == (up ? 1 : -1) ? offset.abs() : BigInteger.ZERO;
        }

        /** The two ends of the form as lines over the whole, each {@code slope}·v +
         *  {@code offset}. */
        record Lines(BigInteger lowSlope, BigInteger lowOffset, BigInteger highSlope,
                     BigInteger highOffset) {}
    }

    /** The runs of {@code values} at which the form between {@code ends} settles
     *  {@code relation}, either way, in order. */
    private static List<SettledRun> settledWithin(WholeRun values, Rel relation,
                                                  Form.Lines ends) {
        List<SettledRun> runs = new ArrayList<>();
        for (boolean holds : List.of(true, false)) {
            for (WholeRun each : whereEveryValueMeets(holds ? relation : relation.denied(),
                    ends.lowSlope(), ends.lowOffset(), ends.highSlope(), ends.highOffset())) {
                WholeRun here = each.meet(values);
                if (here.holdsAWholeNumber()) {
                    runs.add(SettledRun.whole(here.low, here.high, holds));
                }
            }
        }
        return inOrder(runs, true);
    }

    /** {@code before} then {@code after}, the last of the one and the first of the other made one
     *  run where they settle it the same way and meet. */
    private static List<SettledRun> joined(List<SettledRun> before, List<SettledRun> after) {
        List<SettledRun> out = new ArrayList<>(before);
        for (SettledRun each : after) {
            SettledRun last = out.isEmpty() ? null : out.getLast();
            ExactRatio next = last == null ? null : last.to().at().plus(ExactRatio.ONE).orNull();
            if (last != null && last.holds() == each.holds() && next != null
                    && next.equals(each.from().at())) {
                out.set(out.size() - 1, new SettledRun(last.from(), each.to(), each.holds()));
            } else {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * The greatest value of the whole past {@code computed} at which a row computes with the part
     * at its least — {@code computed} where there is none. Past it no row reaches the relation:
     * the addends grow with the whole, so a value at which the least does not compute has none
     * past it that does.
     */
    private static BigInteger reachedUpTo(WholeRun values, BigInteger computed,
                                          WithinTheWhole within, ExactRatio wholeWeight,
                                          ExactRatio partWeight, ExactRatio constant,
                                          Arithmetic arithmetic) {
        BigInteger high = values.high == null ? arithmetic.greatest()
                : values.high.min(arithmetic.greatest());
        BigInteger low = computed;
        while (low.compareTo(high) < 0) {
            BigInteger middle = low.add(high).add(BigInteger.ONE).shiftRight(1);
            if (arithmetic.computes(weighedAt(ExactRatio.of(middle), wholeWeight),
                    weighedAt(ExactRatio.of(within.least()), partWeight), constant)) {
                low = middle;
            } else {
                high = middle.subtract(BigInteger.ONE);
            }
        }
        return low;
    }

    /**
     * The greatest value of the whole up to which every row of {@code values} computes — the whole
     * at each value and the part at each value it takes there — the rows at the least value
     * computing. The greatest of {@code values}, null where it has none, where nothing stops the
     * arithmetic.
     *
     * <p>At one value of the whole the rows are asked at the part's two ends: each addend is a
     * straight function of the part, so the sum of the positive ones and that of the negative ones
     * are greatest at an end. Past the least value no addend's size shrinks as the whole grows —
     * the whole and the part's upper end grow with it, the part's least does not move, and none of
     * them is below nought — so a value whose rows compute has every value below it computing too,
     * and the greatest of them is found by halving.
     */
    private static BigInteger computedUpTo(WholeRun values, WithinTheWhole within,
                                           ExactRatio wholeWeight, ExactRatio partWeight,
                                           ExactRatio constant, Arithmetic arithmetic) {
        if (!arithmetic.stopsAtASize()) {
            return values.high;
        }
        // No whole value past the greatest the type holds is weighed inside it.
        BigInteger high = values.high == null ? arithmetic.greatest()
                : values.high.min(arithmetic.greatest());
        BigInteger low = values.low;
        while (low.compareTo(high) < 0) {
            BigInteger middle = low.add(high).add(BigInteger.ONE).shiftRight(1);
            if (rowsComputeAt(middle, within, wholeWeight, partWeight, constant, arithmetic)) {
                low = middle;
            } else {
                high = middle.subtract(BigInteger.ONE);
            }
        }
        return low;
    }

    /** Whether the rows with the whole at {@code at} compute, the part at either end of what it
     *  takes there. */
    private static boolean rowsComputeAt(BigInteger at, WithinTheWhole within,
                                         ExactRatio wholeWeight, ExactRatio partWeight,
                                         ExactRatio constant, Arithmetic arithmetic) {
        ExactRatio whole = weighedAt(ExactRatio.of(at), wholeWeight);
        return arithmetic.computes(whole, weighedAt(ExactRatio.of(within.least()), partWeight),
                constant)
                && arithmetic.computes(whole, weighedAt(ExactRatio.of(
                        at.subtract(within.belowTheWhole())), partWeight), constant);
    }

    /**
     * The runs of whole numbers v at which every whole number between {@code lowSlope}·v +
     * {@code lowOffset} and {@code highSlope}·v + {@code highOffset} stands to nought as
     * {@code relation} — two runs where it is unequal, the one below nought and the one above.
     */
    private static List<WholeRun> whereEveryValueMeets(Rel relation, BigInteger lowSlope,
                                                       BigInteger lowOffset, BigInteger highSlope,
                                                       BigInteger highOffset) {
        return switch (relation) {
            case LT, LE -> List.of(whereALineStands(highSlope, highOffset, relation));
            case GT, GE -> List.of(whereALineStands(lowSlope, lowOffset, relation));
            case EQ -> List.of(whereALineStands(lowSlope, lowOffset, Rel.GE)
                    .meet(whereALineStands(highSlope, highOffset, Rel.LE)));
            case NE -> List.of(whereALineStands(lowSlope, lowOffset, Rel.GT),
                    whereALineStands(highSlope, highOffset, Rel.LT));
        };
    }

    /** The whole numbers v at which {@code slope}·v + {@code offset} stands to nought as
     *  {@code relation}, an order: every one, none, or the run on one side of a value. */
    private static WholeRun whereALineStands(BigInteger slope, BigInteger offset, Rel relation) {
        if (slope.signum() == 0) {
            return relation.holds(offset.signum()) ? new WholeRun(null, null)
                    : new WholeRun(BigInteger.ONE, BigInteger.ZERO);
        }
        return WholeRun.where(new OnTheDifference(ExactRatio.of(slope), ExactRatio.of(offset),
                relation));
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
     * Whether the factor {@code other} stands strictly on the side {@code relation} needs, and on
     * the other side, of the level over every value of the run {@code between} of the other
     * factor's values of {@code sign} — or, held equal or unequal to nought, at nought and away
     * from it. A value past where its order stops is no witness ({@link Run#passes}).
     */
    private static <P> boolean reachesOverAFactor(Term<P> other, WholeRun between, int sign,
                                                  ExactRatio level, Rel relation) {
        NumericDomain.Bounds realized = other.realizes();
        if (relation == Rel.EQ || relation == Rel.NE) {
            OfNumbers nought = new OfNumbers(ExactRatio.ZERO, ExactRatio.ZERO);
            return !nought.passes(other.runsTo(), other.spacing())
                    && nought.within(realized, Spacings.UNKNOWN)
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
        return !needed.passes(other.runsTo(), other.spacing())
                && needed.around(realized, strictlyBelow(relation, ExactRatio.of(sign)),
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
                                                 Asking asking, BiPredicate<P, P> overlap,
                                                 Independence independent) {
        Term<P> it = terms.get(at);
        Span held = Span.ofTheValues(it.holds());
        Interval rest = constant == null ? null : restOf(terms, at, constant);
        if (held == null || rest == null) {
            return null;
        }
        List<SettledRun> runs = new ArrayList<>();
        List<Span> settledTrue = new ArrayList<>();
        List<Span> between = List.of(held);
        for (boolean holds : List.of(true, false)) {
            Rel asked = holds ? asking.holding() : asking.failing();
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
                    if (asking.apart() && !holds && settledTrue.stream().anyMatch(one ->
                            one.meet(here).occupancy() != Span.Occupancy.EMPTY)) {
                        return null;
                    }
                    if (holds) {
                        settledTrue.add(here);
                    }
                    runs.add(new SettledRun(here.lower(), here.upper(), holds));
                }
            }
        }
        if (runs.isEmpty()) {
            return null;
        }
        for (Span each : between) {
            Interval values = new Interval(each.lower(), each.upper());
            if (!asking.leftBy().stream().allMatch(relation -> reachedBySome(terms, at, values,
                    constant, relation, overlap, independent, null, Arithmetic.ENDLESS))) {
                return null;
            }
        }
        return new Leaves.Settled(inOrder(runs, false), held.lower(), held.upper(), false,
                List.of());
    }

    /** {@code value} weighed {@code weight}, or null where either is no number. */
    private static ExactRatio weighedAt(ExactRatio value, ExactRatio weight) {
        return value == null || weight == null ? null : value.times(weight).orNull();
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
                                             Independence independent, Jointly jointly,
                                             Arithmetic arithmetic) {
        return reachedBySome(terms, at, null, constant, relation, overlap, independent, jointly,
                arithmetic);
    }

    /**
     * The same, asked of the values of the term at {@code at} that lie in {@code within} and not
     * of all it may hold — an exact run, so that an end no decimal writes is still the end.
     *
     * @param arithmetic where the arithmetic of the form stops: a witness passing it is no row
     */
    private static <P> boolean reachedBySome(List<Term<P>> terms, int at, Interval within,
                                             ExactRatio constant, Rel relation,
                                             BiPredicate<P, P> overlap,
                                             Independence independent, Jointly jointly,
                                             Arithmetic arithmetic) {
        boolean[] free = new boolean[terms.size()];
        for (int other = 0; other < terms.size(); other++) {
            free[other] = other != at && apart(terms, other, overlap)
                    && untied(terms, other, independent);
        }
        for (int other = 0; other < terms.size(); other++) {
            if (free[other] && (reaches(terms, other, at, within, constant, relation,
                    List.of(), arithmetic)
                    || reachesWithTheRestHeld(terms, other, at, within, constant, relation,
                            free, arithmetic))) {
                return true;
            }
        }
        return reachedWithoutEnd(terms, relation, free)
                || (within == null && reachedTogether(terms, at, constant, relation, free,
                        jointly))
                || (within == null && reachedPieceByPiece(terms, at, constant, relation, free,
                        arithmetic));
    }

    /**
     * Whether the whole run of the term at {@code at} is cut into pieces each of which some one
     * term apart from it reaches. Which term reaches a value can change along the run: with
     * {@code a + b - s - c >= 0}, {@code b} reaches both sides below {@code c} and {@code s}
     * from there on. A piece is proved by {@link #reaches} asked of that piece alone, so the
     * cuts only decide how much is proved, never whether what is proved holds.
     *
     * <p>The cuts are the values of the term at which a term apart from it stands at an end of
     * its run, or at nought, with the rest of the row at nought, and the whole number after each:
     * a strict relation, or a cut that falls between two whole numbers, moves where the sides
     * change by one.
     */
    private static <P> boolean reachedPieceByPiece(List<Term<P>> terms, int at,
                                                   ExactRatio constant, Rel relation,
                                                   boolean[] free, Arithmetic arithmetic) {
        Term<P> it = terms.get(at);
        Interval run = Interval.of(it.holds());
        if (constant == null || run == null || run.low() == null || run.high() == null
                || it.spacing() != Granularity.DISCRETE || !run.low().isWhole()
                || !run.high().isWhole()) {
            return false;
        }
        BigInteger first = run.low().floor().orNull();
        BigInteger last = run.high().floor().orNull();
        if (first == null || last == null) {
            return false;
        }
        TreeSet<BigInteger> starts = new TreeSet<>();
        starts.add(first);
        for (int other = 0; other < terms.size(); other++) {
            if (!free[other] || terms.get(other).holds() == null) {
                continue;
            }
            Interval held = Interval.of(terms.get(other).holds());
            List<ExactRatio> standsAt = new ArrayList<>(List.of(ExactRatio.ZERO));
            if (held != null && held.low() != null) {
                standsAt.add(held.low());
            }
            if (held != null && held.high() != null) {
                standsAt.add(held.high());
            }
            for (ExactRatio value : standsAt) {
                ExactRatio weighed = weighedAt(value, terms.get(other).weight());
                ExactRatio sum = weighed == null ? null : constant.plus(weighed).orNull();
                ExactRatio cut = sum == null ? null
                        : sum.negated().dividedBy(it.weight()).orNull();
                BigInteger floor = cut == null ? null : cut.floor().orNull();
                if (floor == null) {
                    continue;
                }
                for (int beside = 0; beside <= 1; beside++) {
                    BigInteger start = floor.add(BigInteger.valueOf(beside));
                    if (start.compareTo(first) > 0 && start.compareTo(last) <= 0) {
                        starts.add(start);
                    }
                }
            }
        }
        if (starts.size() < 2) {
            return false;
        }
        List<BigInteger> from = List.copyOf(starts);
        for (int i = 0; i < from.size(); i++) {
            BigInteger to = i + 1 < from.size() ? from.get(i + 1).subtract(BigInteger.ONE) : last;
            Interval piece = new Interval(ExactRatio.of(from.get(i)), ExactRatio.of(to));
            boolean reached = false;
            for (int other = 0; other < terms.size() && !reached; other++) {
                reached = free[other] && (reaches(terms, other, at, piece, constant, relation,
                        List.of(), arithmetic)
                        || reachesWithTheRestHeld(terms, other, at, piece, constant, relation,
                                free, arithmetic));
            }
            if (!reached) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether the term at {@code by} reaches the one at {@code of} with every other term held at
     * one value it takes, chosen so that they come to nought with the constant. The rest standing
     * still, the two are held against nought alone, and {@link #reaches} asks that of two terms.
     * Each of the rest is apart from every term and tied to none, so holding it at one value
     * holds the two at nothing.
     *
     * <p>The rest are held at nought but one, which is held where it brings the constant to
     * nought. Every one of those values is one the term is shown to take. Brought to nought, the
     * constant and the term held against it are still in every row the two are reached with, so
     * they are what a witness of the two is computed beside ({@link #reaches}).
     */
    private static <P> boolean reachesWithTheRestHeld(List<Term<P>> terms, int by, int of,
                                                      Interval within, ExactRatio constant,
                                                      Rel relation, boolean[] free,
                                                      Arithmetic arithmetic) {
        if (terms.size() < 3 || constant == null) {
            return false;
        }
        List<Integer> rest = new ArrayList<>();
        for (int i = 0; i < terms.size(); i++) {
            if (i == by || i == of) {
                continue;
            }
            if (!free[i]) {
                return false;
            }
            rest.add(i);
        }
        for (int last : rest) {
            ExactRatio held = constant.negated().dividedBy(terms.get(last).weight()).orNull();
            if (held != null && takesTheValue(terms.get(last), held) && rest.stream()
                    .allMatch(i -> i == last || takesTheValue(terms.get(i), ExactRatio.ZERO))) {
                ExactRatio beside = held.times(terms.get(last).weight()).orNull();
                if (beside != null && reaches(List.of(terms.get(of), terms.get(by)), 1, 0,
                        within, ExactRatio.ZERO, relation, List.of(constant, beside),
                        arithmetic)) {
                    return true;
                }
                break;
            }
        }
        // Every one of the rest at nought, the constant kept in the row: the row a witness of the
        // two is computed in is then the two and the constant alone.
        return rest.stream().allMatch(i -> takesTheValue(terms.get(i), ExactRatio.ZERO))
                && reaches(List.of(terms.get(of), terms.get(by)), 1, 0, within, constant,
                        relation, List.of(), arithmetic);
    }

    /**
     * Whether {@code term} is shown to take {@code value}: a value of its spacing in the run it
     * takes, at an end only where the run holds the end ({@link Term#realizes}), and one its order
     * holds ({@link Term#runsTo}).
     */
    private static <P> boolean takesTheValue(Term<P> term, ExactRatio value) {
        Interval run = term.realizes() == null ? null : Interval.of(term.realizes());
        if (run == null || term.spacing() == null) {
            return false;
        }
        if (term.spacing() == Granularity.DISCRETE ? !value.isWhole()
                : !value.fitsWrittenDecimal()) {
            return false;
        }
        // Taken only where the term's order holds it, however its run is read.
        if (new OfNumbers(value, value).passes(term.runsTo(), term.spacing())) {
            return false;
        }
        int fromLeast = run.lower() == null ? 1 : value.compareTo(run.lower().at());
        int fromGreatest = run.upper() == null ? -1 : value.compareTo(run.upper().at());
        return (fromLeast > 0 || (fromLeast == 0 && run.lower().inclusive()))
                && (fromGreatest < 0 || (fromGreatest == 0 && run.upper().inclusive()));
    }

    /**
     * Whether an order comes out either way wherever the term asked of stands, because a term
     * apart from every other and tied to none runs on without end in each direction the weighed
     * sum can be taken: wherever the rest stand, it can be put far enough along that the relation
     * comes out that way. One term may do it both ways, or two terms one way each.
     *
     * <p>A term runs on without end where its run is open on that side and so is the order it is
     * counted on ({@link Term#runsTo}): a decimal does. A run open where the representation stops
     * runs out there, and a value of the term asked of whose partner would be past that end is a
     * line and not an end passed over, unless it is beside the end, which {@link #reaches} asks.
     */
    private static <P> boolean reachedWithoutEnd(List<Term<P>> terms, Rel relation,
                                                 boolean[] free) {
        return relation != Rel.EQ && relation != Rel.NE && runsOnWithoutEnd(terms, free, true)
                && runsOnWithoutEnd(terms, free, false);
    }

    /** Whether some term free to stand anywhere it is shown to take runs on without end in the
     *  direction that takes the weighed sum up, for {@code up}, or down. */
    private static <P> boolean runsOnWithoutEnd(List<Term<P>> terms, boolean[] free, boolean up) {
        for (int i = 0; i < terms.size(); i++) {
            Term<P> each = terms.get(i);
            if (!free[i] || each.realizes() == null || each.runsTo() == null) {
                continue;
            }
            boolean towardTheGreatest = up == (each.weight().signum() > 0);
            if (towardTheGreatest ? each.realizes().max() == null && each.runsTo().max() == null
                    : each.realizes().min() == null && each.runsTo().min() == null) {
                return true;
            }
        }
        return false;
    }

    /**
     * Where the arithmetic of the form stops, which every witness stays inside: a row is a witness
     * only where it is computed, whichever way it shows a value taken.
     *
     * <p>For whole numbers that is past the type's greatest value, either way: a number weighed
     * may be worked out with its weight's sign or the other, so a size past the greatest is past
     * the type whichever sign it comes with. What a row adds up — the constant, and each number it
     * holds weighed — stays inside in whatever order it is added where its positive addends
     * together and its negative ones together are no further from nought than the greatest:
     * every sum along the way lies between those two. So addends that cancel are computed, and a
     * size handed in is an addend that might lie either way. Which value of each number a row
     * stands at is the witness's own to say. A type with no greatest ({@link #ENDLESS}) holds no
     * row to a size.
     *
     * @param greatest the greatest value of the type, or null where it has none
     */
    private record Arithmetic(BigInteger greatest) {

        /** A type with no greatest value. */
        static final Arithmetic ENDLESS = new Arithmetic(null);

        static Arithmetic upTo(BigInteger greatest) {
            return greatest == null ? ENDLESS : new Arithmetic(greatest);
        }

        /** Whether it stops at a size, so that a row's sizes say whether it is computed. */
        boolean stopsAtASize() {
            return greatest != null;
        }

        /** Whether a row adding up {@code addends} is computed; an addend that is no number is
         *  no row, where the arithmetic stops at a size. */
        boolean computes(ExactRatio... addends) {
            if (greatest == null) {
                return true;
            }
            ExactRatio up = ExactRatio.ZERO;
            ExactRatio down = ExactRatio.ZERO;
            for (ExactRatio each : addends) {
                if (each == null || up == null || down == null) {
                    return false;
                }
                if (each.signum() > 0) {
                    up = up.plus(each).orNull();
                } else {
                    down = down.plus(each).orNull();
                }
            }
            return up != null && down != null && up.compareTo(ExactRatio.of(greatest)) <= 0
                    && down.negated().compareTo(ExactRatio.of(greatest)) <= 0;
        }
    }

    /**
     * What lets the others be asked together: the type of the relation's terms is whole numbers
     * and the arithmetic on them stops only at a size, so a sum inside it is computed. A type whose
     * arithmetic stops for other reasons than the size of a number — a decimal's scale — has no
     * such size, and a caller that has none passes no {@code Jointly}, so the others are then asked
     * one at a time only.
     */
    private record Jointly(Arithmetic arithmetic) {

        private Jointly {
            if (!arithmetic.stopsAtASize()) {
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
     * <p>A witness is a row that is computed ({@link Arithmetic}): the constant and each term at
     * its farthest value, since the two rows stand at the ends. That is asked of whole numbers
     * only, where the size is all that stops the arithmetic; the values of a term that is not
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
        List<ExactRatio> sizes = new ArrayList<>(List.of(constant.abs()));
        sizes.add(farthestOf(over, it.weight()));
        for (int i = 0; i < terms.size(); i++) {
            if (i == at) {
                continue;
            }
            Term<P> each = terms.get(i);
            Interval taken = wholeRunTakenOnItsOrder(each);
            if (!free[i] || taken == null || !each.weight().isWhole()) {
                return false;
            }
            sum = sum.plus(taken.times(each.weight()));
            if (sum == null) {
                return false;
            }
            sizes.add(farthestOf(taken, each.weight()));
        }
        if (!jointly.arithmetic().computes(sizes.toArray(ExactRatio[]::new))) {
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
     * The values several terms take together, because they are read off one value: the month and
     * the day of one date are two numbers, and not every month goes with every day.
     *
     * <p>Two claims, and the caller makes both or makes no support. Each tuple is one the value
     * gives where the relation is asked, so a combination in it can be asked for as a witness. And
     * every number a term can be appears in some tuple, so that no value of a term goes unasked.
     * The tuples need not be every combination there is — a way that fixes the year of a date
     * leaves the combinations of that year — because a witness is reached by what is listed and
     * what is not listed is asked of no value. A caller that cannot say both makes no support, and
     * the terms are then left to be apart from one another or not asked together.
     *
     * @param terms  the indexes of the terms in the relation's terms, two or more, each once
     * @param tuples the whole-number values of those terms together, in the order of {@code terms}
     */
    public record JointSupport(List<Integer> terms, List<List<ExactRatio>> tuples) {

        public JointSupport {
            terms = List.copyOf(terms);
            tuples = tuples.stream().map(List::copyOf).toList();
            if (terms.size() < 2 || Set.copyOf(terms).size() != terms.size() || tuples.isEmpty()) {
                throw new IllegalArgumentException("a support is two terms or more, each once, with"
                        + " a combination of their values at least: " + terms);
            }
            for (List<ExactRatio> each : tuples) {
                if (each.size() != terms.size() || !each.stream().allMatch(ExactRatio::isWhole)) {
                    throw new IllegalArgumentException(
                            "a combination is a whole number for each term: " + each);
                }
            }
        }
    }

    /** Terms asked together: one support's, or a term alone, whose combinations are its ends. */
    private record Group(List<Integer> members, List<List<ExactRatio>> tuples) {}

    /**
     * Whether the term at {@code at} is reached on both sides of the relation at every value it
     * takes, by terms that are apart from it and each other only as groups: a support's terms are
     * tied to one another, and are asked by the combinations the support gives.
     *
     * <p>At a value of the term, its group's combinations that go with the value are the only ones
     * it may be asked beside. The least and the greatest of the weighed sum there, with the least
     * and the greatest of every other group, are two rows, and the order is monotone in the sum, so
     * the relation comes out one way at the least and the other at the greatest. Each of those is
     * a combination a value gives, or a term's end it is shown to take. The sums are computed, so
     * each stays inside the type as in {@link #reachedTogether}.
     *
     * <p>No group but a support has more than one term, and a term alone is asked as there: held
     * apart from every term of another group and tied to none.
     */
    private static <P> boolean reachedAcrossGroups(List<Term<P>> terms, int at,
                                                   ExactRatio constant, Rel relation,
                                                   BiPredicate<P, P> overlap,
                                                   Independence independent,
                                                   List<JointSupport> supports, Jointly jointly) {
        if (supports.isEmpty() || jointly == null || constant == null || relation == Rel.EQ
                || relation == Rel.NE) {
            return false;
        }
        List<Group> groups = groupsOf(terms, at, supports);
        if (groups == null || !groupsApart(terms, groups, overlap, independent)) {
            return false;
        }
        List<ExactRatio> sizes = new ArrayList<>(List.of(constant.abs()));
        ExactRatio low = constant;
        ExactRatio high = constant;
        Group mine = null;
        for (Group each : groups) {
            if (each.members().contains(at)) {
                mine = each;
            }
            ExactRatio farthest = null;
            ExactRatio least = null;
            ExactRatio greatest = null;
            for (List<ExactRatio> tuple : each.tuples()) {
                ExactRatio away = weighedSum(terms, each.members(), tuple, true);
                ExactRatio sum = weighedSum(terms, each.members(), tuple, false);
                if (away == null || sum == null) {
                    return false;
                }
                farthest = farthest == null || away.compareTo(farthest) > 0 ? away : farthest;
                least = least == null || sum.compareTo(least) < 0 ? sum : least;
                greatest = greatest == null || sum.compareTo(greatest) > 0 ? sum : greatest;
            }
            sizes.add(farthest);
            if (each != mine) {
                low = low.plus(least).orNull();
                high = high.plus(greatest).orNull();
                if (low == null || high == null) {
                    return false;
                }
            }
        }
        if (!jointly.arithmetic().computes(sizes.toArray(ExactRatio[]::new))) {
            return false;
        }
        int column = mine.members().indexOf(at);
        Set<ExactRatio> values = new LinkedHashSet<>();
        for (List<ExactRatio> tuple : mine.tuples()) {
            values.add(tuple.get(column));
        }
        boolean strictAtLeast = relation == Rel.LT || relation == Rel.GE;
        for (ExactRatio value : values) {
            ExactRatio least = null;
            ExactRatio greatest = null;
            for (List<ExactRatio> tuple : mine.tuples()) {
                if (!tuple.get(column).equals(value)) {
                    continue;
                }
                ExactRatio sum = weighedSum(terms, mine.members(), tuple, false);
                least = least == null || sum.compareTo(least) < 0 ? sum : least;
                greatest = greatest == null || sum.compareTo(greatest) > 0 ? sum : greatest;
            }
            ExactRatio atLeast = low.plus(least).orNull();
            ExactRatio atMost = high.plus(greatest).orNull();
            if (atLeast == null || atMost == null
                    || !(strictAtLeast ? atLeast.signum() < 0 : atLeast.signum() <= 0)
                    || !(strictAtLeast ? atMost.signum() >= 0 : atMost.signum() > 0)) {
                return false;
            }
        }
        return true;
    }

    /**
     * The supports and, for every term they leave out, the term alone, or null where a support is
     * not a set of distinct terms of the relation, or a term that is asked cannot be asked as its
     * ends: the term at {@code at} by what it holds, the others by what they are shown to take,
     * and all of them weighed by a whole number.
     */
    private static <P> List<Group> groupsOf(List<Term<P>> terms, int at,
                                            List<JointSupport> supports) {
        boolean[] covered = new boolean[terms.size()];
        List<Group> out = new ArrayList<>();
        for (JointSupport each : supports) {
            for (int member : each.terms()) {
                if (member < 0 || member >= terms.size() || covered[member]
                        || !terms.get(member).weight().isWhole()) {
                    return null;
                }
                covered[member] = true;
            }
            out.add(new Group(each.terms(), each.tuples()));
        }
        for (int i = 0; i < terms.size(); i++) {
            if (covered[i]) {
                continue;
            }
            Term<P> each = terms.get(i);
            Interval run = i == at ? wholeRunOf(each.holds(), each.spacing())
                    : wholeRunTakenOnItsOrder(each);
            if (run == null || !each.weight().isWhole()) {
                return null;
            }
            out.add(new Group(List.of(i),
                    List.of(List.of(run.low()), List.of(run.high()))));
        }
        return out;
    }

    /** Whether every term of a group is apart from every term of each other group, and tied to
     *  none of them. */
    private static <P> boolean groupsApart(List<Term<P>> terms, List<Group> groups,
                                           BiPredicate<P, P> overlap, Independence independent) {
        for (int a = 0; a < groups.size(); a++) {
            for (int b = a + 1; b < groups.size(); b++) {
                for (int one : groups.get(a).members()) {
                    for (int other : groups.get(b).members()) {
                        if (!independent.between(one, other)
                                || !apartPlaces(terms.get(one), terms.get(other), overlap)) {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }

    private static <P> boolean apartPlaces(Term<P> one, Term<P> other, BiPredicate<P, P> overlap) {
        for (P first : one.madeOf()) {
            for (P second : other.madeOf()) {
                if (overlap.test(first, second)) {
                    return false;
                }
            }
        }
        return true;
    }

    /** The values of {@code tuple} weighed and added — or their sizes, for {@code absolute} — or
     *  null where that is no number. */
    private static <P> ExactRatio weighedSum(List<Term<P>> terms, List<Integer> members,
                                             List<ExactRatio> tuple, boolean absolute) {
        ExactRatio sum = ExactRatio.ZERO;
        for (int k = 0; k < members.size() && sum != null; k++) {
            ExactRatio weight = terms.get(members.get(k)).weight();
            ExactRatio value = tuple.get(k);
            ExactRatio part = (absolute ? value.abs().times(weight.abs())
                    : value.times(weight)).orNull();
            sum = part == null ? null : sum.plus(part).orNull();
        }
        return sum;
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

    /**
     * The whole numbers {@code term} is shown to take, on the order it stands on: a position read
     * as though its order ran on is cut to where its order stops, since a witness stands on a
     * value the type has. Null where nothing is shown of the term.
     */
    private static <P> Interval wholeRunTakenOnItsOrder(Term<P> term) {
        if (term.realizes() == null) {
            return null;
        }
        NumericDomain.Bounds taken = endsAtNumbers(term.runsTo())
                ? term.realizes().meet(term.runsTo())
                : term.realizes();
        return wholeRunOf(taken, term.spacing());
    }

    /** The weighed size of {@code run}'s farthest value from nought, or null where that is no
     *  number. */
    private static ExactRatio farthestOf(Interval run, ExactRatio weight) {
        ExactRatio low = run.low().abs();
        ExactRatio farthest = low.compareTo(run.high().abs()) >= 0 ? low : run.high().abs();
        return farthest.times(weight.abs()).orNull();
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
     * A run whose ends are where the representation stops, and not lines of anything compared.
     *
     * <p>The reading of two terms by their difference passes over the values beside the ends of
     * what the terms take. That is the representation running out of partners and not a line the
     * model draws, which holds of the ends of a type and of the year of a date, and does not hold
     * of a month of twelve or a length of nought: a value at either settles the comparison for a
     * reason of its own. The caller says which it has by handing the run over in this type, and so
     * by having shown it.
     *
     * @param run the run the terms take, open on a side it does not stop on
     */
    public record WhereTheRepresentationStops(NumericDomain.Bounds run) {

        public WhereTheRepresentationStops {
            if (run == null) {
                throw new IllegalArgumentException("a run the representation stops on is a run");
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
     * <p><b>Beside the ends, and no further in.</b> A row at a value is computed where its addends
     * are ({@link Arithmetic}). Weighed by one, the two are the values themselves and the row
     * comes to the difference and the constant, so a row passes the type only at a value within
     * those of an end, which is beside it. Any other weight multiplies the values, and the rows
     * passing the type are those of every value whose weighed size does — half the type at a
     * weight of two. So under any other weight the rows are asked at both ends of the run, and
     * nothing is shown where one of them is not computed.
     *
     * @param terms    two terms, each the value at its place or a number taken of one, taking
     *                 every value of its type and the same values as the other — or nothing is
     *                 shown
     * @param held     every statement the rows arriving hold of either term, each about their
     *                 difference
     * @param extent   where the values the two take stop
     * @param overlap  whether two places are one, or one is part of the other
     * @param greatest the greatest value the type the form is worked out in holds, or null where
     *                 it holds no greatest
     */
    public static <P> Set<P> ofTheirDifference(List<Term<P>> terms, ExactRatio constant,
                                               Rel relation, List<OnTheDifference> held,
                                               WhereTheRepresentationStops extent,
                                               BiPredicate<P, P> overlap, BigInteger greatest) {
        if (terms.size() != 2 || constant == null || !apart(terms, 0, overlap)
                || !moveTogether(terms.get(0), terms.get(1), extent.run())
                || !(terms.get(0).weight().abs().equals(ExactRatio.ONE)
                        || rowsComputeAtTheEnds(terms.get(0).weight(), constant, extent.run(),
                                Arithmetic.upTo(greatest)))) {
            return Set.of();
        }
        WholeRun middle = WholeRun.reachedFromTheMiddleOf(extent.run());
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
     * Whether the rows of two terms weighed {@code weight} and its negation, held against
     * {@code constant}, are computed at both ends of {@code run}: the first at the end, the second
     * a difference from it a step either side of where the relation turns. Each addend is a
     * straight function of the value, so rows computed at both ends are computed between them.
     */
    private static boolean rowsComputeAtTheEnds(ExactRatio weight, ExactRatio constant,
                                                NumericDomain.Bounds run,
                                                Arithmetic arithmetic) {
        if (!arithmetic.stopsAtASize()) {
            return true;
        }
        Interval ends = Interval.of(run);
        ExactRatio turns = constant.negated().dividedBy(weight).orNull();
        if (ends == null || ends.low() == null || ends.high() == null || turns == null) {
            return false;
        }
        for (ExactRatio value : List.of(ends.low(), ends.high())) {
            for (ExactRatio apart : new ExactRatio[] {turns.minus(ExactRatio.ONE).orNull(),
                    turns.plus(ExactRatio.ONE).orNull()}) {
                ExactRatio first = value.times(weight).orNull();
                ExactRatio second = apart == null ? null
                        : value.minus(apart).flatMap(other -> other.times(weight.negated()))
                                .orNull();
                if (!arithmetic.computes(first, second, constant)) {
                    return false;
                }
            }
        }
        return true;
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
    private static <P> boolean moveTogether(Term<P> one, Term<P> other,
                                            NumericDomain.Bounds extent) {
        return reachesTheWholeType(one, extent) && reachesTheWholeType(other, extent)
                && one.itsPlace() == other.itsPlace()
                && one.takes() != null && one.takes().equals(other.takes())
                && one.weight().plus(other.weight()) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio sum)
                && sum.signum() == 0;
    }

    /**
     * Whether the term is shown to take every value of the type it is a value of: the value at its
     * place says nothing of where it lies, and what is taken of a place is shown to take all of
     * {@code extent}.
     */
    private static <P> boolean reachesTheWholeType(Term<P> term, NumericDomain.Bounds extent) {
        return term.realizes() != null
                && (term.itsPlace() ? term.realizes().saysNothing()
                        : term.realizes().equals(extent));
    }

    /**
     * Whether the term at {@code by} stands wherever the relation needs it to for the term at
     * {@code of} to be left undivided.
     *
     * <p>A witness is a row that is computed ({@link #aWitnessComputes}), asked last, of an
     * answer that would otherwise be yes: most terms are refused by something cheaper first.
     *
     * @param beside     the addends the row holds besides the two and the constant — the terms
     *                   held still beside them, each weighed — or none
     * @param arithmetic where the arithmetic of the form stops
     */
    private static <P> boolean reaches(List<Term<P>> terms, int by, int of, Interval within,
                                       ExactRatio constant, Rel relation, List<ExactRatio> beside,
                                       Arithmetic arithmetic) {
        Term<P> reaching = terms.get(by);
        boolean exactly = relation == Rel.EQ || relation == Rel.NE;
        boolean itsValue = standsAtTheOthersValue(terms, constant);
        if (exactly && itsValue && sameValues(terms, by, of)) {
            return aWitnessComputes(terms, by, of, within, constant, relation, beside, arithmetic);
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
        // A value past where the reaching term's order stops is no witness, however its run is
        // read (asARelationReadsIt): an end of the type moved by a constant or a weight, a value
        // weighed past it, an end of the other's order the reaching term's runs out before. Only
        // a term standing at the other's value passes over an end, where its order runs on as
        // far as the other's: there a value with no partner is beside the end of both.
        if (needed.passes(reaching.runsTo(), reaching.spacing())
                && !(itsValue && runsOnAsFar(reaching, terms.get(of)))) {
            return false;
        }
        if (exactly) {
            return needed.within(reaching.realizes(), spacings)
                    && aWitnessComputes(terms, by, of, within, constant, relation, beside, arithmetic);
        }
        boolean strictlyBelow = strictlyBelow(relation, reaching.weight());
        if ((strictlyBelow ? needed.runsDown() : needed.runsUp())
                && !othersAreTheirPlaces(terms, by)) {
            return false;
        }
        return needed.around(reaching.realizes(), strictlyBelow, spacings)
                && aWitnessComputes(terms, by, of, within, constant, relation, beside, arithmetic);
    }

    /**
     * Whether the order {@code reaching} is counted on runs on at least as far as the one
     * {@code other} is, each way. Where the reaching term stands at the other's value, an end of
     * the type is passed over only so: past where the reaching term's order stops, a value of the
     * other has no partner, and that is a line of the relation and not an end passed over.
     */
    private static <P> boolean runsOnAsFar(Term<P> reaching, Term<P> other) {
        // Two orders stopping at the same ends, numbers or not — two strings — run on together.
        if (reaching.runsTo() != null && reaching.runsTo().equals(other.runsTo())) {
            return true;
        }
        Interval mine = reaching.runsTo() == null ? null : Interval.of(reaching.runsTo());
        Interval theirs = other.runsTo() == null ? null : Interval.of(other.runsTo());
        return mine != null && theirs != null
                && (mine.lower() == null || (theirs.lower() != null
                        && mine.lower().at().compareTo(theirs.lower().at()) <= 0))
                && (mine.upper() == null || (theirs.upper() != null
                        && mine.upper().at().compareTo(theirs.upper().at()) >= 0));
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

    /**
     * Whether a run ending at {@code cut}, its values spaced as {@code spacing}, holds a value past
     * {@code end} — above it, or below it. An end missing on either is nothing past.
     */
    private static boolean pastTheEnd(ExactCut cut, ExactCut end, Granularity spacing,
                                      boolean above) {
        if (cut == null || end == null) {
            return false;
        }
        ExactRatio last = cut.at();
        boolean in = cut.inclusive();
        if (spacing == Granularity.DISCRETE) {
            // The whole number the run's values end at on that side.
            BigInteger whole = above
                    ? (in ? cut.at().floor().orNull()
                            : cut.at().ceiling().map(c -> c.subtract(BigInteger.ONE)).orNull())
                    : (in ? cut.at().ceiling().orNull()
                            : cut.at().floor().map(f -> f.add(BigInteger.ONE)).orNull());
            if (whole == null) {
                return false;
            }
            last = ExactRatio.of(whole);
            in = true;
        }
        int toward = above ? last.compareTo(end.at()) : end.at().compareTo(last);
        return toward > 0 || (toward == 0 && in && !end.inclusive());
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
        Interval at = neededAt(terms, by, of, within, constant);
        return at == null ? null : at.asRun();
    }

    /**
     * Where the term at {@code by} has to stand, as a run of numbers, for the term at {@code of}
     * to be at its values — those in {@code within}, where that is given — and every other term
     * anywhere it may be: null where one of them, or the constant, is no number.
     */
    private static <P> Interval neededAt(List<Term<P>> terms, int by, int of, Interval within,
                                         ExactRatio constant) {
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
        ExactRatio turned = ExactRatio.ONE.negated().dividedBy(terms.get(by).weight()).orNull();
        return turned == null ? null : rest.times(turned);
    }

    /**
     * Whether, at every value of the term at {@code of} asked of, the rows the term at {@code by}
     * reaches it in are computed ({@link Arithmetic}) — a row on each side of the line, which is
     * what a value left either way is.
     *
     * <p>At a value of the one, the other stands at the last value on one side of the line and the
     * first on the other ({@link #acrossTheLine}), every other term at its value nearest nought,
     * and {@code beside} with them. Each addend of such a row is a value of the one weighed, or
     * the line over it a fixed way off, so each is the same straight function of the value, and
     * so is the sum of the positive ones and of the negative ones. Those are computed at every
     * value of a run where they are at its two ends, and there the rows are asked.
     * {@code 2^62 x - 2^62 y < 0}, {@code x} from nought to one, has both
     * rows at nought and none on the true side at one, where a {@code y} of two weighed passes the
     * type; {@code x - y > M}, {@code M} the greatest {@code Int}, has a true row at no {@code x}.
     * A run open on a side has no end to ask, and nothing is shown.
     *
     * <p>Two terms standing at each other's value with nothing besides are compared and not
     * added, and are asked nothing of it.
     *
     * @param beside the addends a row holds besides the two and the constant — the terms held
     *               still beside them, each weighed
     */
    private static <P> boolean aWitnessComputes(List<Term<P>> terms, int by, int of,
                                                Interval within, ExactRatio constant,
                                                Rel relation, List<ExactRatio> beside,
                                                Arithmetic arithmetic) {
        if (!arithmetic.stopsAtASize() || (standsAtTheOthersValue(terms, constant)
                && beside.stream().allMatch(each -> each.signum() == 0))) {
            return true;
        }
        Interval asked = within != null ? within : Interval.of(terms.get(of).holds());
        if (constant == null || asked == null || asked.low() == null || asked.high() == null) {
            return false;
        }
        List<ExactRatio> fixed = new ArrayList<>(beside);
        fixed.add(constant);
        for (int i = 0; i < terms.size(); i++) {
            if (i != by && i != of) {
                fixed.add(weighedAt(nearestValue(Interval.of(terms.get(i).holds())),
                        terms.get(i).weight()));
            }
        }
        for (ExactRatio value : List.of(asked.low(), asked.high())) {
            List<ExactRatio> row = new ArrayList<>(fixed);
            row.add(weighedAt(value, terms.get(of).weight()));
            ExactRatio rest = ExactRatio.ZERO;
            for (ExactRatio each : row) {
                rest = each == null || rest == null ? null : rest.plus(each).orNull();
            }
            ExactRatio line = rest == null ? null
                    : rest.negated().dividedBy(terms.get(by).weight()).orNull();
            List<ExactRatio> across = line == null ? null
                    : acrossTheLine(line, relation, terms.get(by));
            if (across == null) {
                return false;
            }
            for (ExactRatio at : across) {
                List<ExactRatio> witness = new ArrayList<>(row);
                witness.add(at.times(terms.get(by).weight()).orNull());
                if (!arithmetic.computes(witness.toArray(ExactRatio[]::new))) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Where {@code reaching} stands in a row on each side of {@code line} for {@code relation}:
     * the last value of its spacing on one side and the first on the other — or null where they
     * are no number. A whole term weighed so that the side strictly past the line is below it
     * stands one below the least whole number at or past the line, and at it; otherwise at the
     * greatest at or before the line, and one above it. Held equal or unequal, the line is a value
     * and one beside it; a term whose values are dense stands as near the line as asked.
     */
    private static <P> List<ExactRatio> acrossTheLine(ExactRatio line, Rel relation,
                                                      Term<P> reaching) {
        if (reaching.spacing() != Granularity.DISCRETE) {
            return List.of(line);
        }
        if (relation == Rel.EQ || relation == Rel.NE) {
            ExactRatio next = line.plus(ExactRatio.ONE).orNull();
            return next == null ? null : List.of(line, next);
        }
        BigInteger from = strictlyBelow(relation, reaching.weight())
                ? line.ceiling().map(at -> at.subtract(BigInteger.ONE)).orNull()
                : line.floor().orNull();
        return from == null ? null
                : List.of(ExactRatio.of(from), ExactRatio.of(from.add(BigInteger.ONE)));
    }

    /** The value of {@code run} nearest nought, or null where the run is no run of numbers. */
    private static ExactRatio nearestValue(Interval run) {
        if (run == null) {
            return null;
        }
        if (run.low() != null && run.low().signum() > 0) {
            return run.low();
        }
        if (run.high() != null && run.high().signum() < 0) {
            return run.high();
        }
        return ExactRatio.ZERO;
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

        /**
         * Whether some value of this run, taken by a term spaced as {@code spacing}, lies past
         * where {@code order} stops. A run open on a side runs past every end; with no order
         * known, or ends that are no numbers, only such a run is said to.
         */
        default boolean passes(NumericDomain.Bounds order, Granularity spacing) {
            if (runsDown() || runsUp()) {
                return true;
            }
            Interval stops = order == null ? null : Interval.of(order);
            return stops != null && (pastTheEnd(upperCut(), stops.upper(), spacing, true)
                    || pastTheEnd(lowerCut(), stops.lower(), spacing, false));
        }

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

        /** Whether every whole number of {@code other} is one of this run's. */
        boolean covers(WholeRun other) {
            return (low == null || (other.low != null && low.compareTo(other.low) <= 0))
                    && (high == null || (other.high != null && high.compareTo(other.high) >= 0));
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
