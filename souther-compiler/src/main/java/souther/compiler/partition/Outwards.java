package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.values.ValueSet;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

/**
 * The values of a run tried in order, from one of them outward.
 *
 * <p>The searches that sample a run need this and none of them needs a proof out of it. Where the
 * candidates come from is each one's own question — the places two positions both admit, the values
 * of one position that leave the rest a residue their coefficients land on, the values a region
 * still leaves it — and once there is a value to start from and a distance between the next ones,
 * what is left is the order they are tried in.
 *
 * <p><b>Outward and not upward.</b> A run this is asked about has at least one end missing or it
 * would be walked rather than sampled, and which end that is says nothing about where the answer
 * lies. Going one way only, a search over a run open below never reaches a value under the one it
 * started from.
 *
 * <p><b>How many is the caller's and not this one's.</b> What stepping past a value buys, and
 * therefore how many steps are worth taking, depends on what takes values out of the middle of a
 * run — and its callers do not have one answer to that. Nothing here is a proof at any length.
 */
final class Outwards {

    private Outwards() {
    }

    /**
     * The places walked, and how the walk came to end.
     *
     * <p>Two halves of one answer. A caller reading only the first cannot tell a run with nothing
     * further in it from one this stopped walking, and the three mean different things about an
     * empty hand.
     *
     * <p><b>No word for "not all of them", which is what a caller has to be stopped from asking
     * for.</b> Two of the endings answer that alike and are what a reader does two different things
     * about, so a caller handed the question in that shape names one of them for the other: the
     * pair search took an order with no step and a figure met for one fact, and told a reader to
     * raise a number that reaches nothing. So what is offered is the ending itself, and every
     * caller says what it does with each.
     */
    record Walked(List<Place> places, Ended ended) implements Iterable<Place> {

        Walked {
            places = List.copyOf(places);
        }

        /** The places, so that a caller wanting only those walks this. */
        @Override
        public java.util.Iterator<Place> iterator() {
            return places.iterator();
        }
    }

    /**
     * How a walk came to end.
     *
     * <p><b>Four, because three of them are limits and no two are the same limit.</b> A figure is a
     * number somebody wrote down and raising it walks further; an order with no step is one this has
     * no way of naming another place on, and raising anything reaches none of them
     * ({@link CompositionRepertoire}). Held as one boolean, the last was reported as a figure —
     * a reader told to raise a number that stopped nothing — or as neither, which is a walk of one
     * place claiming to have walked them all.
     *
     * <p><b>And the two figures are two.</b> Taking as many places as were asked for and walking
     * past as many as were allowed are different stops with different numbers behind them: one is
     * raised to try more of what was found, the other to look further for something to find. They
     * were one ending while every place of the run was a place to take, and the narrowings a run
     * has no word for are what separated them.
     */
    enum Ended {

        /** Neither direction had a place left, so what came back is every place there was. */
        HAVING_TRIED_THEM_ALL,

        /** As many places were taken as the caller asked for, and the run holds another. */
        AT_THE_FIGURE_OF_CANDIDATES,

        /** As many places of the run were walked past as the caller allowed, without that many
         *  being taken. What stopped this is the looking and not what was found. */
        AT_THE_FIGURE_OF_PLACES_LOOKED_AT,

        /** This order has no step to take, so what came back is the one place this could name and
         *  whether the run holds others is not something this walked. */
        WITH_NO_STEP_TO_TAKE
    }

    /**
     * At most {@code howManyPlaces} places of {@code within} that {@code admits} takes in and none
     * of {@code apart} stands at, from {@code first} outward, {@code by} apart.
     *
     * <p>Stops early where neither direction has a place left, which is what makes a bounded run
     * cost its own width rather than the whole allowance.
     *
     * <p><b>Every narrowing, and not the run on its own.</b> A run says where a position stops and
     * has no word for the values the declarations leave it or for a place a rule took out of the
     * middle of it. Walked by the run alone, the places after the first come from one narrowing and
     * are judged by the others afterwards — which is the trade this walk's own caller was written
     * to avoid at the place it starts from, made again at every place after it. So the narrowings
     * arrive together and a caller cannot ask for a walk that leaves one out.
     *
     * <p>A place the run holds and one of the others refuses is stepped past. It is not the run
     * running out, so the walk goes on, and it is not a place to try, so it is not yielded.
     *
     * @param first         a place the run holds and the narrowings take in. Refused where it is
     *                      none, since a caller with no place to start from has composed nothing —
     *                      which is not the same as a run with nothing in it, and an empty answer
     *                      here would be read as the second
     * @param by            the distance between neighbouring candidates, positive
     * @param howManyTaken  how many places to take, counting {@code first}. What a caller spends
     *                      on putting them to the rest of its question
     * @param howManyLookedAt how many places of the run to walk past, counting {@code first}. What
     *                      a caller spends on the walking, which the one above stopped bounding the
     *                      moment a place of the run stopped being a place to take. Needed on its
     *                      own because a run with no end whose places the narrowings all refuse is
     *                      otherwise a walk nothing stops
     */
    static Walked from(Place first, Count by, Carrier carrier, NumericDomain.Bounds within,
                       int howManyTaken, int howManyLookedAt, ValueSet admits, PlacesApart apart) {
        if (by == null || by.signum() <= 0) {
            throw new IllegalArgumentException(
                    "neighbouring candidates are a positive distance apart, or there is no outward:"
                            + " " + by);
        }
        if (first == null || !takenIn(first, carrier, within, admits, apart)) {
            throw new IllegalArgumentException(
                    "walking outward starts from a place every narrowing takes in, and a caller that"
                            + " has none has composed nothing rather than found a run with nothing"
                            + " in it: " + first);
        }
        // One place where the carrier's values do not count. There is no next place to step to, so
        // the one the caller started from is the whole of what this can name — and never the whole
        // of what the run holds, which is why it ends its own way. Reported as a walk that tried
        // them all, a pair the rules leave a place for anywhere but here came back as a pair
        // nothing could build.
        //
        // Unless the run is that one place, and then there is nothing further for a way of naming
        // one to reach. Said the other way, a run bounded to a single value would have this
        // compiler reporting a population it writes some of — of a walk that wrote all of it.
        if (!carrier.counts()) {
            return new Walked(List.of(first), onePlace(within, first)
                    ? Ended.HAVING_TRIED_THEM_ALL : Ended.WITH_NO_STEP_TO_TAKE);
        }
        List<Place> out = new ArrayList<>();
        out.add(first);
        int lookedAt = 1;
        // <b>A value found and not taken, never a count that came out even.</b> A run holding
        // exactly this many and a run this stopped walking come back the same length, so the figure
        // being reached says nothing on its own — what says this compiler declined to go further is
        // a value the run holds that this did not take. Read off the count instead, a run walked to
        // its end reports a budget nobody reached, and a point nothing could stop is reported as one
        // this stopped: the same trade this file is here to prevent, made the other way round.
        Ended ended = Ended.HAVING_TRIED_THEM_ALL;
        outward:
        for (int step = 1; ; step++) {
            BigDecimal away = BigDecimal.valueOf(step);
            Place[] neighbours = {
                    carrier.onTheGrid(Count.number(first).plus(by.times(away))),
                    carrier.onTheGrid(Count.number(first).minus(by.times(away)))};
            boolean took = false;
            for (Place next : neighbours) {
                if (next == null || !within.admits(next)) {
                    continue;
                }
                // A place of the run, so the run has not run out and the walk goes on whether or
                // not this one is taken.
                took = true;
                // Refused by one of the narrowings the run has no word for, which is a place to
                // step past rather than a place to try. Yielded, it would be a candidate the rules
                // refuse, offered because the run happened to hold it. What it spends is the
                // looking, and it is the looking that has to stop somewhere.
                if (!takenIn(next, carrier, within, admits, apart)) {
                    if (++lookedAt >= howManyLookedAt) {
                        ended = Ended.AT_THE_FIGURE_OF_PLACES_LOOKED_AT;
                        break outward;
                    }
                    continue;
                }
                if (out.size() == howManyTaken) {
                    // One the run holds, this takes in, and is not taking.
                    ended = Ended.AT_THE_FIGURE_OF_CANDIDATES;
                    break outward;
                }
                out.add(next);
                if (++lookedAt >= howManyLookedAt) {
                    ended = Ended.AT_THE_FIGURE_OF_PLACES_LOOKED_AT;
                    break outward;
                }
            }
            if (!took) {
                break;   // neither direction has a place left, so this walked the whole of it
            }
        }
        return new Walked(out, ended);
    }

    /**
     * Whether every narrowing takes {@code at} in.
     *
     * <p>One place the answer is decided, so that the place a walk starts from and the places it
     * steps to are held to the same thing. Asked of the carrier for the set, because which values
     * an order writes at a place is the carrier's answer and not a comparison anybody here can
     * make.
     */
    private static boolean takenIn(Place at, Carrier carrier, NumericDomain.Bounds within,
                                   ValueSet admits, PlacesApart apart) {
        return within.admits(at) && carrier.admitted(admits, at) && !apart.has(at);
    }

    /**
     * Whether the run is the one place already in hand.
     *
     * <p>Both ends the place itself and both of them its own, which is the only shape an order with
     * no arithmetic can be asked about: anything else needs a comparison this would have to make
     * with the order's own values, and the caller already holds what came of asking that.
     */
    private static boolean onePlace(NumericDomain.Bounds within, Place first) {
        return within.min() != null && within.max() != null
                && within.min().inclusive() && within.max().inclusive()
                && within.min().at().sameAs(first) && within.max().at().sameAs(first);
    }
}
