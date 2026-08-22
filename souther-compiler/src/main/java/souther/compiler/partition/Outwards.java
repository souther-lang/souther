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
 * <p>Both searches over a line need this and neither of them needs a proof out of it. Where the
 * candidates come from is each one's own question — the places two positions both admit, or the
 * values of one position that leave the rest a residue their coefficients land on — and once there
 * is a value to start from and a distance between the next ones, what is left is the order they are
 * tried in.
 *
 * <p><b>Outward and not upward.</b> A run this is asked about has at least one end missing or it
 * would be walked rather than sampled, and which end that is says nothing about where the answer
 * lies. Going one way only, a search over a run open below never reaches a value under the one it
 * started from.
 *
 * <p><b>How many is the caller's and not this one's.</b> What stepping past a value buys, and
 * therefore how many steps are worth taking, depends on what takes values out of the middle of a
 * run — and the two callers do not have the same answer to that. Nothing here is a proof at any
 * length.
 */
final class Outwards {

    private Outwards() {
    }

    /**
     * At most {@code howManyValues} values of {@code within}, from {@code first} outward, {@code by}
     * apart.
     *
     * <p>Stops early where neither direction has a value left, which is what makes a bounded run
     * cost its own width rather than the whole allowance.
     *
     * @param first         a value of the run, which the caller has one of before it asks
     * @param by            the distance between neighbouring candidates, positive
     * @param howManyValues how many to yield, counting {@code first}
     */
    static List<Place> from(Place first, Count by, Carrier carrier, NumericDomain.Bounds within,
                            int howManyValues) {
        if (first == null) {
            return List.of();
        }
        // One place where the carrier's values do not count. There is no next place to step to, so
        // the one the caller started from is the whole of what there is to try.
        if (!carrier.counts()) {
            return List.of(first);
        }
        List<Place> out = new ArrayList<>();
        out.add(first);
        for (int step = 1; out.size() < howManyValues; step++) {
            BigDecimal away = BigDecimal.valueOf(step);
            Place above = carrier.onTheGrid(Count.number(first).plus(by.times(away)));
            Place below = carrier.onTheGrid(Count.number(first).minus(by.times(away)));
            boolean took = false;
            if (above != null && within.admits(above)) {
                out.add(above);
                took = true;
            }
            if (below != null && within.admits(below) && out.size() < howManyValues) {
                out.add(below);
                took = true;
            }
            if (!took) {
                break;
            }
        }
        return List.copyOf(out);
    }
}
