package souther.compiler.coverage;

import java.util.Set;

/**
 * What one run of one row was seen to do, as a value nothing goes on changing.
 *
 * <p>One snapshot and not two channels. What is recorded has two shapes — the places a run passed
 * through, and the ways the comparisons it evaluated came out — and they are taken together, of one
 * thread, between one {@code begin} and one {@code end}. Handed over as two values they would be two
 * things a reader could get from different runs, and a reader that asked for one of them would be
 * reasoning about a run it had only half of.
 *
 * <p>{@link #comparisons} implies {@link #taken}: a way a comparison came out is recorded by the
 * same call that records the comparison having been reached, so a run holding the first without the
 * second is one nothing produces. That holds by how the recording is written rather than by a rule
 * the emitter is asked to keep, which is the difference between an invariant and a convention.
 *
 * @param taken       the sites the run was recorded at, which is what a branch measure counts and
 *                    what a boundary drawn on a guard is met by
 * @param comparisons the ways the comparisons it evaluated came out
 */
public record Observation(Set<Integer> taken, Set<ComparisonOutcome> comparisons) {

    /** A run nothing was recorded of, which is what a caller with no measuring build has. */
    public static final Observation NONE = new Observation(Set.of(), Set.of());

    public Observation {
        taken = taken == null ? Set.of() : Set.copyOf(taken);
        comparisons = comparisons == null ? Set.of() : Set.copyOf(comparisons);
    }

    /** Whether the run was recorded at {@code site}. */
    public boolean lit(int site) {
        return taken.contains(site);
    }

    /** Whether the run had {@code way} happen. Not the same as its comparison having been reached:
     *  a comparison that came out the other way was reached and is not this. */
    public boolean saw(ComparisonOutcome way) {
        return comparisons.contains(way);
    }

    /** Whether the run reached {@code comparison} at all, whichever way it came out. */
    public boolean reached(ComparisonOccurrence comparison) {
        return lit(comparison.emissionSite());
    }
}
