package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.semantics.Arithmetic;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

/**
 * The whole number a run holds that leaves the remainders asked for, found by solving for it.
 *
 * <p>What a remainder asks of a value is a class of whole numbers, and what several of them ask is
 * the class the congruences meet in ({@link Congruences}) — or nothing, where they disagree. So the
 * value is arithmetic on the numbers the demands name and not a walk through the places a run holds:
 * how far apart those are is the product of the divisors, and a walk that is allowed a figure of
 * steps is no way to find a number that is a few dozen steps from where it starts and a million from
 * where it ends.
 *
 * <p><b>The numbers each demand names are the only thing enumerated.</b> A demand is a set of
 * remainders, and a remainder is below its divisor, so it has as many to choose from as the set
 * holds. A figure bounds how many of them are tried; every one of them is a class, and a class meets
 * the run in a number that is read off its end. The combinations of the demands' choices are tried in
 * order, a choice that disagrees with an earlier one is dropped where it is made, and where every
 * combination there is was tried the answer is that there is no such number.
 *
 * <p>Said as three answers and not a number or its absence: a search that stopped at its figure has
 * not shown that there is none, and a reader told so would say the rules leave nothing where this
 * compiler left something untried.
 */
final class RemainderSolutions {

    private RemainderSolutions() {
    }

    /**
     * One remainder asked for.
     *
     * @param divisor the divisor, with its sign: the remainder takes the divisor's side of nought
     * @param wanted  the remainders that would do
     * @param named   the remainder a caller picked to try first, or null
     */
    record Demand(BigDecimal divisor, NumericSet wanted, Place named) {}

    /** What came of solving. */
    sealed interface Answer {

        /** This number of the run leaves every remainder asked for. */
        record Found(BigInteger value) implements Answer {}

        /** There is no such number: every combination of the demands' remainders was tried. */
        record NoneThere() implements Answer {}

        /** Some remainders were not tried, which a figure of this compiler's stopped. */
        record Undecided(CompositionBudget figure) implements Answer {}
    }

    /**
     * The remainders of one demand to try.
     *
     * @param stoppedBy the figure that left some of the demand's remainders unlooked at, or null
     *                  where these are every one it admits
     */
    private record Choices(List<BigInteger> remainders, CompositionBudget stoppedBy) {}

    /**
     * What the rules leave of the value the remainders are of.
     *
     * @param run      where the value runs
     * @param standing the class the remainders already fixed beside it hold it to, or null where
     *                 there is none
     * @param refuses  whether the rules leave nothing where the value stands at a number, which a
     *                 run does not say: a class has another member to offer where its nearest one
     *                 is a number the rules refuse
     */
    record Value(NumericDomain.Bounds run, Congruences standing, Predicate<Place> refuses) {}

    /**
     * The number of the value's run that leaves what {@code demands} ask, where {@code carrier} is
     * the order the numbers are counted on.
     *
     * <p>The class the value is already held to is one more thing the number must leave, met with
     * the demands' as theirs are with each other: a number named for the demands alone is one the
     * fixed remainders refuse. And a member of the class the rules refuse, as a hole in the run
     * does, is stepped past to the next member, so that what stands in the way of the nearest
     * member is not taken for the class having none.
     */
    static Answer solve(List<Demand> demands, Value value, Carrier carrier) {
        List<Choices> choices = new ArrayList<>();
        List<BigInteger> sizes = new ArrayList<>();
        CompositionBudget stopped = null;
        for (Demand demand : demands) {
            BigInteger size = Arithmetic.AFloorRemainder.magnitudeOf(demand.divisor());
            if (size == null) {
                return new Answer.NoneThere();
            }
            Choices here = choicesOf(demand, size, carrier);
            stopped = stopped != null ? stopped : here.stoppedBy();
            choices.add(here);
            sizes.add(size);
        }
        // How many combinations of the demands' choices are tried: the compiler's one figure for the
        // steps of a search, which numbers of a set looked at below are counted against as well.
        int steps = CompositionBudget.STEPS_A_SEARCH_MAY_TAKE.maximum();
        int[] tried = {0};
        BigInteger found = search(choices, sizes, 0, value.standing(), value, tried, steps, null);
        if (found != null) {
            return new Answer.Found(found);
        }
        if (tried[0] > steps) {
            return new Answer.Undecided(CompositionBudget.STEPS_A_SEARCH_MAY_TAKE);
        }
        return stopped == null ? new Answer.NoneThere() : new Answer.Undecided(stopped);
    }

    /** The first number of the run that leaves a remainder of each demand from {@code at} on, given
     *  the class {@code met} the earlier ones left, or null where there is none. */
    private static BigInteger search(List<Choices> choices, List<BigInteger> sizes, int at,
                                     Congruences met, Value value, int[] tried, int steps,
                                     BigInteger last) {
        if (at == choices.size()) {
            // A remainder is a number of the place when the run is open, and the number nearest to
            // nought in its class is the remainder itself: a row for a remainder of nought up to
            // seven is the number it asks for and not one seven above it. Which holds where one
            // remainder is asked and nothing else holds the value to a class.
            BigInteger own = choices.size() == 1 && value.standing() == null
                    ? last : null;
            return ++tried[0] > steps ? null : inTheRun(met, value, own, tried, steps);
        }
        for (BigInteger remainder : choices.get(at).remainders()) {
            // Every choice looked at is a step, the ones that disagree with an earlier choice
            // included: a demand whose choices never agree with the last demand's would otherwise
            // be walked in full and counted as nothing.
            if (++tried[0] > steps) {
                return null;
            }
            Congruences here = new Congruences(remainder, sizes.get(at));
            Congruences next = met == null ? here : met.meet(here);
            if (next == null) {
                continue;
            }
            BigInteger found = search(choices, sizes, at + 1, next, value, tried, steps, remainder);
            if (found != null || tried[0] > steps) {
                return found;
            }
        }
        return null;
    }

    /**
     * The remainders {@code demand} admits, the one a caller named first and then the least ones in
     * order, as many as a figure allows.
     *
     * <p>A remainder is from nought up to the divisor, not reaching it, and from the divisor up to
     * nought, not reaching it, for a divisor below nought. Which of those the demand holds is asked
     * of its set, and the set's own ends say where to begin.
     */
    private static Choices choicesOf(Demand demand, BigInteger size, Carrier carrier) {
        boolean positive = demand.divisor().signum() > 0;
        BigInteger least = positive ? BigInteger.ZERO : size.subtract(BigInteger.ONE).negate();
        BigInteger most = positive ? size.subtract(BigInteger.ONE) : BigInteger.ZERO;
        int allowed = CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum();
        List<BigInteger> found = new ArrayList<>();
        BigInteger named = demand.named() instanceof Count count && count.exactly().isWhole()
                && count.exactly().floor() instanceof ExactAnswer.Held<BigInteger> whole
                ? whole.value() : null;
        if (named != null && admits(demand, named, least, most, carrier)) {
            found.add(named);
        }
        NumericDomain.Bounds extent = demand.wanted().extent();
        BigInteger from = lowestWholeNumberOf(extent.min());
        BigInteger to = highestWholeNumberOf(extent.max());
        BigInteger at = from == null || from.compareTo(least) < 0 ? least : from;
        BigInteger last = to == null || to.compareTo(most) > 0 ? most : to;
        int looked = 0;
        int lookedAtMost = CompositionBudget.STEPS_A_SEARCH_MAY_TAKE.maximum();
        for (; at.compareTo(last) <= 0 && found.size() < allowed && looked < lookedAtMost;
                at = at.add(BigInteger.ONE), looked++) {
            if (!at.equals(named) && admits(demand, at, least, most, carrier)) {
                found.add(at);
            }
        }
        // Every one there is only where the walk reached the end of the range: it stopped short of
        // that at the number of remainders it was allowed to try, or at the numbers it was allowed
        // to look at, and which of the two it was is what a reader may raise.
        CompositionBudget stoppedBy = at.compareTo(last) > 0 ? null
                : found.size() >= allowed ? CompositionBudget.NUMBERS_OF_A_SET_TRIED
                        : CompositionBudget.STEPS_A_SEARCH_MAY_TAKE;
        return new Choices(List.copyOf(found), stoppedBy);
    }

    private static boolean admits(Demand demand, BigInteger remainder, BigInteger least,
                                  BigInteger most, Carrier carrier) {
        if (remainder.compareTo(least) < 0 || remainder.compareTo(most) > 0) {
            return false;
        }
        Place place = carrier.onTheGrid(new Count(new BigDecimal(remainder)));
        return place != null && demand.wanted().holds(place, carrier);
    }

    /**
     * The member of {@code members} nearest the end {@code run} has, or null where it holds none.
     *
     * <p>Found by arithmetic: the least member at or above the run's lower end, the greatest at or
     * below its upper end where it has no lower one, and where it has neither the class's own least
     * non-negative member — or {@code own}, a member the caller would have first where the run is
     * open.
     *
     * <p>The members the rules refuse are passed over, each a step of the search, so that a figure
     * stops a class that has nothing else to offer and does not leave it said to hold nothing.
     */
    static BigInteger inTheRun(Congruences members, Value value, BigInteger own, int[] tried,
                               int steps) {
        BigInteger low = lowestWholeNumberOf(value.run().min());
        BigInteger high = highestWholeNumberOf(value.run().max());
        boolean upward = low != null || high == null;
        BigInteger member = low != null ? members.leastAtOrAbove(low)
                : high != null ? members.greatestAtOrBelow(high)
                : own != null ? own : members.residue();
        while (value.refuses().test(new Count(new BigDecimal(member)))) {
            if (++tried[0] > steps) {
                return null;
            }
            member = upward ? member.add(members.modulus()) : member.subtract(members.modulus());
            if (upward && high != null && member.compareTo(high) > 0) {
                return null;
            }
        }
        return upward && high != null && member.compareTo(high) > 0 ? null : member;
    }

    /** The first whole number {@code end} admits, or null where it has none to name. */
    static BigInteger lowestWholeNumberOf(Endpoint end) {
        if (end == null || !(end.at() instanceof Count count)
                || !(count.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger> edge)) {
            return null;
        }
        return !end.inclusive() && count.exactly().isWhole()
                ? edge.value().add(BigInteger.ONE) : edge.value();
    }

    /** The last whole number {@code end} admits, or null where it has none to name. */
    static BigInteger highestWholeNumberOf(Endpoint end) {
        if (end == null || !(end.at() instanceof Count count)
                || !(count.exactly().floor() instanceof ExactAnswer.Held<BigInteger> edge)) {
            return null;
        }
        return !end.inclusive() && count.exactly().isWhole()
                ? edge.value().subtract(BigInteger.ONE) : edge.value();
    }
}
