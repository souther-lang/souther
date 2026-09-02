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

    /** An empty snapshot: a run recorded as having passed nowhere. Not the same as having no
     *  account of a run at all, which is not something this can say and is said where a run is
     *  handed over. */
    public static final Observation NONE = new Observation(Set.of(), Set.of());

    public Observation {
        taken = taken == null ? Set.of() : Set.copyOf(taken);
        comparisons = comparisons == null ? Set.of() : Set.copyOf(comparisons);
        // Held here and not left to whoever records one. What a recording is written like is a
        // producer's business and can change; that a way out of a comparison means the comparison
        // was reached is what every reader of this is entitled to, and a value that broke it would
        // certify a claim about a place the same value says was never got to.
        //
        // Both ways out of one comparison together are not a breach and must not be refused: a
        // place a run comes back to is evaluated more than once, and a recording that held only
        // which way it went the first time would be saying less than it saw.
        for (ComparisonOutcome way : comparisons) {
            if (!taken.contains(way.at().value())) {
                throw new IllegalArgumentException(
                        "a run that saw " + way + " is one that reached " + way.at());
            }
        }
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

    /** Whether the run reached {@code site} at all, whichever way the comparison there came out. */
    public boolean reached(ComparisonEmissionSite site) {
        return lit(site.value());
    }
}
