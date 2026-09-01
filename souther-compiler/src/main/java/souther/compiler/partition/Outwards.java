package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;

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
     * The places walked, and whether there were more this stopped short of.
     *
     * <p>Two halves of one answer. A caller reading only the first cannot tell a run with nothing
     * further in it from one this stopped walking, and only the second of those is a figure
     * somebody could raise.
     */
    record Walked(List<Place> places, boolean stoppedShort) implements Iterable<Place> {

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
     * At most {@code howManyValues} values of {@code within}, from {@code first} outward, {@code by}
     * apart.
     *
     * <p>Stops early where neither direction has a value left, which is what makes a bounded run
     * cost its own width rather than the whole allowance.
     *
     * @param first         a value of the run. Refused where it is none, since a caller with no
     *                      value to start from has composed nothing — which is not the same as a run
     *                      with nothing in it, and an empty answer here would be read as the second
     * @param by            the distance between neighbouring candidates, positive
     * @param howManyValues how many to yield, counting {@code first}
     */
    static Walked from(Place first, Count by, Carrier carrier, NumericDomain.Bounds within,
                       int howManyValues) {
        if (by == null || by.signum() <= 0) {
            throw new IllegalArgumentException(
                    "neighbouring candidates are a positive distance apart, or there is no outward:"
                            + " " + by);
        }
        if (first == null || !within.admits(first)) {
            throw new IllegalArgumentException(
                    "walking outward starts from a value of the run, and a caller that has none has"
                            + " composed nothing rather than found a run with nothing in it: "
                            + first);
        }
        // One place where the carrier's values do not count. There is no next place to step to, so
        // the one the caller started from is the whole of what there is to try.
        if (!carrier.counts()) {
            return new Walked(List.of(first), false);
        }
        List<Place> out = new ArrayList<>();
        out.add(first);
        // <b>A value found and not taken, never a count that came out even.</b> A run holding
        // exactly this many and a run this stopped walking come back the same length, so the figure
        // being reached says nothing on its own — what says this compiler declined to go further is
        // a value the run holds that this did not take. Read off the count instead, a run walked to
        // its end reports a budget nobody reached, and a point nothing could stop is reported as one
        // this stopped: the same trade this file is here to prevent, made the other way round.
        boolean stoppedShort = false;
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
                if (out.size() == howManyValues) {
                    stoppedShort = true;   // one the run holds and this is not taking
                    break outward;
                }
                out.add(next);
                took = true;
            }
            if (!took) {
                break;   // neither direction has a value left, so this walked the whole of it
            }
        }
        return new Walked(out, stoppedShort);
    }
}
