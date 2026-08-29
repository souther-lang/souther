package souther.compiler.partition;

import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;

import java.util.ArrayList;
import java.util.List;

/**
 * How a row for one border came to be looked for where it is: every condition on the way, in the
 * order the walk met them.
 *
 * <p>An account and not a place. Where a row is looked for is {@link #narrowing(SearchRegion)} and
 * {@link #requirements()} of what the declarations leave, and those are worked out from this
 * whenever somebody needs them — so they cannot come to say different things, because there is only
 * one of them. A pair kept side by side would be values that have to agree and nothing able to check
 * that they do: {@link SearchRegion} answers questions about values and does not say which
 * conditions it was built from, on purpose.
 *
 * <p><b>Two vocabularies, because a condition lands in one of them or in neither.</b> What a
 * comparison states is an inequality over numbers and what a fork states is which case a value
 * turned out to be, and neither says the other: a region has no word for a case, and a narrowing
 * orders nothing. So a search composing a row against this reads both, and what it still does not
 * represent is {@link #declined()}.
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

    /**
     * What has to be true of the parameters for a row to reach the border, off the narrowings the
     * way took in.
     *
     * <p>The other half of what a region is. A region says which numbers a position may hold and has
     * no word for which case a value turned out to be, so a fork on the way lands here — and a
     * composer holding both is holding the whole of what this reading could state.
     *
     * <p>Or nothing, where two narrowings on the way cannot hold together. That is a way no row
     * takes, which is a fact about the model and not something to compose against: read as an
     * absence of requirements, a row would be composed for a border down a path nothing reaches.
     */
    public Requirements.Merge requirements() {
        Requirements out = Requirements.NONE;
        for (OnTheWay each : onTheWay) {
            if (each instanceof OnTheWay.Narrowed narrowed) {
                Requirements.Merge both = out.merge(narrowed.position().requirements());
                if (!(both instanceof Requirements.Merge.Merged merged)) {
                    return both;
                }
                out = merged.requirements();
            }
        }
        return new Requirements.Merge.Merged(out);
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

    /** The ones this reading could state in neither vocabulary, which is what a search composing
     *  against both of them still does not represent. */
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
