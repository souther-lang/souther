package souther.compiler.partition;

import souther.compiler.inputs.SearchRegion;

import java.util.ArrayList;
import java.util.List;

/**
 * Where a row for one border is looked for, and how that came to be the place.
 *
 * <p>Three things hold of every one of these, and the first two are {@link SearchRegion}'s own:
 *
 * <pre>what reaches the border ⊆ where ⊆ what the declarations leave</pre>
 *
 * <p>and {@code where} is {@code base} with exactly the {@link OnTheWay.TakenIn} entries of
 * {@code provenance} taken in, in the order they are written. A {@link OnTheWay.Declined} entry
 * never narrows {@code where} — it is the record that something on the way is not represented in
 * it.
 *
 * <p><b>Made here and nowhere else.</b> A region and an account of it are two values that have to
 * say the same thing, and nothing can check that they do: {@link SearchRegion} answers questions
 * about values and does not say which conditions it was built from, on purpose, so a pair handed in
 * from outside could disagree with no reader able to tell. So the pair is not constructible — only
 * narrowed, which builds one from the other.
 *
 * <p>What a report may say from this is what the entries say and no more. That some condition was
 * declined does not make {@code where} wider than the rows that reach the border: a condition the
 * arithmetic could not take in may have been implied by the ones it did, or may hold everywhere.
 * What is known is that not everything on the way is represented here.
 */
public final class RegionForARow {

    private final SearchRegion where;
    private final List<OnTheWay> provenance;

    private RegionForARow(SearchRegion where, List<OnTheWay> provenance) {
        this.where = where;
        this.provenance = provenance;
    }

    /** {@code base} with the cuts of {@code provenance} taken in, carrying the whole of it. */
    public static RegionForARow narrowed(SearchRegion base, List<OnTheWay> provenance) {
        SearchRegion region = base;
        for (OnTheWay each : provenance) {
            if (each instanceof OnTheWay.TakenIn taken) {
                region = region.assuming(taken.cut().form(), taken.cut().rel());
            }
        }
        return new RegionForARow(region, List.copyOf(provenance));
    }

    /**
     * {@code base} with nothing on the way to take in.
     *
     * <p>Which is a border of a rule that is about the values rather than about a place in a body:
     * an invariant holds wherever a value stands, so there is nowhere for a row to have come from.
     * Said by the empty account rather than by the absence of one.
     */
    public static RegionForARow untouched(SearchRegion base) {
        return narrowed(base, List.of());
    }

    /** Where a row is looked for. */
    public SearchRegion where() {
        return where;
    }

    /** Every condition on the way to the border, in the order the walk met them. */
    public List<OnTheWay> provenance() {
        return provenance;
    }

    /** The ones that narrowed {@link #where()}. */
    public List<OnTheWay.TakenIn> takenIn() {
        List<OnTheWay.TakenIn> out = new ArrayList<>();
        for (OnTheWay each : provenance) {
            if (each instanceof OnTheWay.TakenIn taken) {
                out.add(taken);
            }
        }
        return List.copyOf(out);
    }

    /** The ones that did not, which is what is not represented in {@link #where()}. */
    public List<OnTheWay.Declined> declined() {
        List<OnTheWay.Declined> out = new ArrayList<>();
        for (OnTheWay each : provenance) {
            if (each instanceof OnTheWay.Declined left) {
                out.add(left);
            }
        }
        return List.copyOf(out);
    }
}
