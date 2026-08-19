package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.BoundaryDomain;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Place;

import java.math.BigDecimal;
import java.util.Optional;

/**
 * How one {@link BorderQuantity}'s own values are ordered, and which of them the quantity can take.
 *
 * <p><b>Three questions, and they are not one.</b> Whether the quantity can take a level at all
 * ({@link #attainable}), whether a level has one next to it ({@link #neighbour}), and whether
 * anything at all lies past it ({@link #anythingBeyond}). A decimal difference is attainable
 * everywhere, has a neighbour nowhere, and has values on both sides of every level. Answered as one
 * question, a border over decimals lost its {@code IN} point along with the point beside its line,
 * and a line at a string lost the whole of the side above it — because a string has no successor.
 *
 * <p>And attainability is not adjacency. {@code 2 * a <= 9} cuts a quantity whose values are the even
 * numbers: the threshold is a level the quantity never takes, and the border is still there, with its
 * {@code ON} point at 8 and its {@code OFF} point at 10. A reader that assumed the threshold was one
 * of the quantity's own values would put a row at 9 and call the rule exercised.
 *
 * <p>Not sealed, and never switched on. Which of these a quantity has is the quantity's own answer
 * and no reader's question: a reader that asked would be asking which variant the quantity is under
 * another name, which is the shape this whole arrangement exists to stop.
 *
 * <p>What it says is about the order alone — the ambient one, before any rule narrows anything. What
 * the rules leave is a separate answer and belongs to whatever holds them: a level this says exists
 * may be one no row can be written at, and that is {@link Realization}'s to report rather than a
 * reason to move the level.
 */
public interface LevelSpace {

    /**
     * Whether {@code l} is below, at or above {@code r}.
     *
     * <p>Both on this space. Two levels of different spaces are never compared — the mistake is this
     * compiler's rather than anything a model can write, and it is said as one, the way
     * {@link Place#notOneOrder} says it of two carriers' places.
     */
    int compare(Level l, Level r);

    /** Whether the quantity can take this level at all. */
    boolean attainable(Level level);

    /**
     * The nearest level the quantity can take at or past {@code from}, the way {@code towards} says,
     * or empty where the order names none there.
     *
     * <p>What both points of a border are found with: the threshold itself where the quantity takes
     * it, and the first value it does take otherwise.
     */
    Optional<Level> nearestAtOrBeyond(Level from, Towards towards);

    /**
     * The nearest level this quantity can take strictly past {@code from}, the way {@code towards}
     * says, or empty where the order names no single value there.
     *
     * <p>Adjacency, and nothing else. Empty says the space has no <em>next</em> value, which is not
     * a statement that it has no value that way: a decimal difference has no successor and has
     * every larger difference. {@link #anythingBeyond} is that other question.
     */
    Optional<Level> neighbour(Level from, Towards towards);

    /**
     * Some level this quantity takes strictly past {@code from}, the way {@code towards} says, or
     * empty where it takes none.
     *
     * <p>A witness of the side and not the side itself: a row at any level past the end is at the
     * point, and the one offered here is a candidate. Which is why it is apart from
     * {@link #neighbour} — a side wants any level that way and a point wants the one next to it, and
     * an order whose values fill has the first and not the second. Asked for the neighbour, every
     * side of every border over decimals came back with nothing tried.
     */
    Optional<Level> somethingBeyond(Level from, Towards towards);

    /**
     * Whether this quantity takes any value at all strictly past {@code from}, the way
     * {@code towards} says.
     *
     * <p>What decides whether a border has a side there. False only where the order itself stops —
     * an enumeration at its last case, a string a rule holds another string apart from — and never
     * because the step between two values has no name.
     */
    boolean anythingBeyond(Level from, Towards towards);

    /**
     * The values of one coordinate, which are the values of the carrier it is ordered by.
     *
     * <p>The one space whose levels a carrier can write. Its neighbours are the carrier's own
     * ({@link BoundaryDomain}), so a date steps a day and a decimal steps nowhere; what it can take
     * is what the carrier holds on its grid, since not every number between two of a carrier's
     * counts is one of them; and its ends are the carrier's extent.
     */
    static LevelSpace onACarrier(Carrier carrier) {
        BoundaryDomain steps = BoundaryDomain.on(carrier);
        OrderedInterval extent = carrier == null ? OrderedInterval.OPEN : carrier.extent();
        return new LevelSpace() {

            @Override
            public int compare(Level l, Level r) {
                return placeOf(l).compareTo(placeOf(r));
            }

            @Override
            public boolean attainable(Level level) {
                return carrier != null && carrier.onTheGrid(placeOf(level)) != null;
            }

            /**
             * The level itself where the carrier holds it, and the first count it does hold that way
             * otherwise.
             *
             * <p>Rounded the way {@code towards} asks and never the other way. Not every number
             * between two of a carrier's counts is one of them — halfway between two moments is a
             * number and not a date-time — and a threshold written between two of them has its two
             * points either side of it, not both on whichever side rounding happened to land.
             */
            @Override
            public Optional<Level> nearestAtOrBeyond(Level from, Towards towards) {
                if (attainable(from)) {
                    return Optional.of(from);
                }
                if (carrier == null || !(placeOf(from) instanceof Count count)) {
                    return Optional.empty();   // an order with no numbers holds what it holds
                }
                Place rounded = carrier.onTheGrid(count.rounded(towards == Towards.ABOVE
                        ? java.math.RoundingMode.CEILING : java.math.RoundingMode.FLOOR));
                return rounded == null ? Optional.empty()
                        : Optional.of(new Level.OnACarrier(carrier, rounded));
            }

            @Override
            public Optional<Level> neighbour(Level from, Towards towards) {
                Optional<Place> next = towards == Towards.ABOVE
                        ? steps.successor(placeOf(from)) : steps.predecessor(placeOf(from));
                return next.map(at -> new Level.OnACarrier(carrier, at));
            }

            @Override
            public Optional<Level> somethingBeyond(Level from, Towards towards) {
                Optional<Level> next = neighbour(from, towards);
                if (next.isPresent() || !anythingBeyond(from, towards)) {
                    return next;
                }
                Endpoint past = Endpoint.exclusive(placeOf(from));
                Place inside = towards == Towards.ABOVE
                        ? carrier.somethingInside(past, extent.high())
                        : carrier.somethingInside(extent.low(), past);
                return Optional.ofNullable(inside).map(at -> new Level.OnACarrier(carrier, at));
            }

            @Override
            public boolean anythingBeyond(Level from, Towards towards) {
                Endpoint past = Endpoint.exclusive(placeOf(from));
                return towards == Towards.ABOVE
                        ? Endpoint.someValueLiesBetween(past, extent.high())
                        : Endpoint.someValueLiesBetween(extent.low(), past);
            }

            private Place placeOf(Level level) {
                if (!(level instanceof Level.OnACarrier on)) {
                    throw new IllegalStateException(
                            "a coordinate's order was asked about a level that is not one of its "
                                    + "values: " + level);
                }
                return on.at();
            }
        };
    }

    /**
     * The numbers a quantity counts to, {@code step} apart, taking every multiple of the step.
     *
     * <p>What two positions on an order that steps stand apart, and what an affine form over whole
     * coordinates comes to. The step is the quantity's and not any position's: two positions on a
     * carrier that steps stand one apart and one apart is the whole of the difference, while
     * {@code 300x + 600y} moves in three hundreds however small a step {@code x} takes.
     */
    static LevelSpace steppingBy(BigDecimal step) {
        return new Counting() {

            @Override
            public boolean attainable(Level level) {
                BigDecimal at = countOf(level).at();
                return at.remainder(step).signum() == 0;
            }

            @Override
            public Optional<Level> nearestAtOrBeyond(Level from, Towards towards) {
                if (attainable(from)) {
                    return Optional.of(from);
                }
                BigDecimal at = countOf(from).at();
                BigDecimal whole = at.divide(step, 0, towards == Towards.ABOVE
                        ? java.math.RoundingMode.CEILING : java.math.RoundingMode.FLOOR);
                return Optional.of(new Level.ACount(new Count(whole.multiply(step))));
            }

            @Override
            public Optional<Level> neighbour(Level from, Towards towards) {
                Level at = nearestAtOrBeyond(from, towards).orElseThrow();
                BigDecimal here = countOf(at).at();
                // From where the quantity actually is, and not from where the threshold was written.
                // A threshold the quantity never takes has its two points either side of it, and the
                // point past it is one step from the value on that side rather than one step from a
                // number nothing stands at.
                if (compare(at, from) != 0) {
                    return Optional.of(at);
                }
                return Optional.of(new Level.ACount(new Count(
                        towards == Towards.ABOVE ? here.add(step) : here.subtract(step))));
            }
        };
    }

    /**
     * The numbers a quantity counts to where the order names no step between them.
     *
     * <p>Every number is a level and none of them has a next one. What a rule holding two decimals
     * apart cuts: the pair one step further apart is not a pair this language names, and every pair
     * further apart than the line is one it does.
     */
    static LevelSpace dense() {
        return new Counting() {

            @Override
            public boolean attainable(Level level) {
                countOf(level);
                return true;
            }

            @Override
            public Optional<Level> nearestAtOrBeyond(Level from, Towards towards) {
                countOf(from);
                return Optional.of(from);
            }

            @Override
            public Optional<Level> neighbour(Level from, Towards towards) {
                countOf(from);
                return Optional.empty();
            }
        };
    }

    /**
     * The one level a quantity can take, on an order that has sides all the same.
     *
     * <p>What two strings a rule holds apart come to. There is no number between them, so the only
     * level the quantity takes is the one where they meet; and one string is still above another, so
     * both sides of that level are inhabited. Read as an order with nothing past its only value, a
     * rule written {@code a > b} over strings would owe no {@code IN} point at all.
     */
    static LevelSpace onlyWhereTheyMeet() {
        return new Counting() {

            @Override
            public boolean attainable(Level level) {
                return countOf(level).signum() == 0;
            }

            @Override
            public Optional<Level> nearestAtOrBeyond(Level from, Towards towards) {
                return attainable(from) ? Optional.of(from) : Optional.empty();
            }

            @Override
            public Optional<Level> neighbour(Level from, Towards towards) {
                countOf(from);
                return Optional.empty();
            }

            /** Only where they meet is a level here, so there is none past it — and both sides of
             *  it are still inhabited, which {@link #anythingBeyond} is what says. */
            @Override
            public Optional<Level> somethingBeyond(Level from, Towards towards) {
                countOf(from);
                return Optional.empty();
            }
        };
    }

    /**
     * The step a lattice made by these coefficients moves in: their greatest common divisor.
     *
     * <p>Bézout's, and exact rather than a guess: what {@code Σ cᵢ·xᵢ} takes over the whole numbers
     * is exactly the multiples of {@code gcd(cᵢ)}. Taken over them as whole numbers at their common
     * scale, so a decimal coefficient answers the way a whole one does.
     *
     * <p>Here rather than on the quantity, because it is what makes the space and a search prunes by
     * it as well: a residue that is not one of these multiples is one no assignment lands on.
     */
    static BigDecimal stepOf(java.util.Collection<BigDecimal> coefs) {
        int scale = 0;
        for (BigDecimal coef : coefs) {
            scale = Math.max(scale, Math.max(coef.scale(), 0));
        }
        java.math.BigInteger together = java.math.BigInteger.ZERO;
        for (BigDecimal coef : coefs) {
            together = together.gcd(coef.setScale(scale).unscaledValue().abs());
        }
        return new BigDecimal(together, scale);
    }

    /** The shared half of every space whose levels are numbers: how two of them compare, and that a
     *  number always has numbers either side of it. What stops a border having a side on one of
     *  these is what the rules leave, which is asked of them and not of the order. */
    abstract class Counting implements LevelSpace {

        @Override
        public int compare(Level l, Level r) {
            return countOf(l).compareTo(countOf(r));
        }

        @Override
        public boolean anythingBeyond(Level from, Towards towards) {
            countOf(from);
            return true;
        }

        /**
         * The next level where the order steps, and one step of the numbers themselves where it does
         * not.
         *
         * <p>Any level past the end witnesses the side, so where the order names no next one this
         * offers a number that is past it and says no more than that. Offered as the item it would
         * be wrong; offered as a candidate for a side, one number past is as good as any other.
         */
        @Override
        public Optional<Level> somethingBeyond(Level from, Towards towards) {
            Optional<Level> next = neighbour(from, towards);
            if (next.isPresent()) {
                return next;
            }
            return Optional.of(new Level.ACount(countOf(from)
                    .plus(towards == Towards.ABOVE ? 1 : -1)));
        }

        static Count countOf(Level level) {
            if (!(level instanceof Level.ACount count)) {
                throw new IllegalStateException(
                        "a counted order was asked about a level that is not a number: " + level);
            }
            return count.at();
        }
    }
}
