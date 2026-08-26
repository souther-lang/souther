package souther.compiler.partition;

import souther.compiler.inputs.SearchRegion;

import java.util.ArrayList;
import java.util.List;

/**
 * How a row for one border came to be looked for where it is: every condition on the way, in the
 * order the walk met them.
 *
 * <p>An account and not a place. Where a row is looked for is {@link #narrowing(SearchRegion)} of
 * what the declarations leave, and that is worked out from this whenever somebody needs it — so the
 * two cannot come to say different things, because there is only one of them. A pair of the two kept
 * side by side would be two values that have to agree and nothing able to check that they do:
 * {@link SearchRegion} answers questions about values and does not say which conditions it was built
 * from, on purpose.
 *
 * <p><b>This is what an answer keeps.</b> A region is a way of asking rather than something that
 * says what it is, and one kept in an answer carries the whole reading of a module's rules — down to
 * the store the reading was made against — into a value two compilations of one source have to
 * compare equal. What a reader of a finished search wants from it is what the way declined, which is
 * here; what a search wants is the region, and a search is where the region is built.
 *
 * <p>What a report may say from this is what the entries say and no more. That some condition was
 * declined does not make the region wider than the rows that reach the border: a condition the
 * arithmetic could not take in may have been implied by the ones it did, or may hold everywhere.
 * What is known is that not everything on the way is represented in it.
 */
public record WayToTheBorder(List<OnTheWay> onTheWay) {

    /** Nothing on the way to take in.
     *
     * <p>Which is a border of a rule that is about the values rather than about a place in a body:
     * an invariant holds wherever a value stands, so there is nowhere for a row to have come from.
     * Said by the empty account rather than by the absence of one. */
    public static final WayToTheBorder UNTOUCHED = new WayToTheBorder(List.of());

    public WayToTheBorder {
        onTheWay = List.copyOf(onTheWay);
    }

    /**
     * {@code base} with exactly the {@link OnTheWay.TakenIn} entries taken in, in the order they are
     * written.
     *
     * <p>Three things hold of what comes back, and the first two are {@link SearchRegion}'s own:
     *
     * <pre>what reaches the border ⊆ this ⊆ what the declarations leave</pre>
     *
     * <p>A {@link OnTheWay.Declined} entry never narrows it — it is the record that something on the
     * way is not represented in what comes back.
     */
    public SearchRegion narrowing(SearchRegion base) {
        SearchRegion region = base;
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.TakenIn taken) {
                region = region.assuming(taken.cut().form(), taken.cut().rel());
            }
        }
        return region;
    }

    /** The ones that narrow a region built from this. */
    public List<OnTheWay.TakenIn> takenIn() {
        List<OnTheWay.TakenIn> out = new ArrayList<>();
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.TakenIn taken) {
                out.add(taken);
            }
        }
        return List.copyOf(out);
    }

    /** The ones that do not, which is what such a region does not represent. */
    public List<OnTheWay.Declined> declined() {
        List<OnTheWay.Declined> out = new ArrayList<>();
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.Declined left) {
                out.add(left);
            }
        }
        return List.copyOf(out);
    }
}
