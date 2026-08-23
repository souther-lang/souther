package souther.compiler.query;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Everything that leaves one measurement weaker than it looks, and the one way measurements are put
 * together.
 *
 * <p>A parent measure's account of itself is the union of what its parts went without. That is the
 * whole of the arithmetic: a report adding up nine measures asks each of them what weakened it and
 * unions the answers, where it used to ask each of them a boolean and rebuild the boolean from the
 * fields beside it.
 *
 * <p><b>A set and not a list.</b> The same fact reaching a parent by two paths is one fact — a rule
 * this compiler could not read leaves the partition measure short at every position it bears on —
 * and a parent that reported it twice would be counting the paths. So union is idempotent,
 * commutative and associative, and two sets holding the same facts are one value whatever order they
 * were found in.
 *
 * <p><b>Order is kept anyway.</b> Equality is the set's, so the order is not part of the value; the
 * order the readers found things in is what a document prints, and a run that produced them in a
 * different order each time is a report that cannot be compared with the last one.
 *
 * <p>A value, because these travel inside {@code Db} answers. An answer that never equals its own
 * recomputation is one {@code Db} reports as changed on every run, and everything that read it runs
 * again over a model nobody edited — which {@code MeasureClosure.Closed} was already arranged
 * against.
 */
public record WeakeningSet(Set<Weakening> causes) {

    private static final WeakeningSet NONE = new WeakeningSet(Set.of());

    public WeakeningSet {
        causes = causes == null ? Set.of()
                : Collections.unmodifiableSet(new LinkedHashSet<>(causes));
    }

    /** Nothing weakened it, which is what a complete measurement has and what a measurement nobody
     *  asked for has. */
    public static WeakeningSet none() {
        return NONE;
    }

    public static WeakeningSet of(Weakening... causes) {
        return new WeakeningSet(new LinkedHashSet<>(java.util.Arrays.asList(causes)));
    }

    public static WeakeningSet ofAll(Collection<? extends Weakening> causes) {
        return new WeakeningSet(new LinkedHashSet<>(causes));
    }

    /** Both, as one. The identity is {@link #none()}, and a fact in both sides arrives once. */
    public WeakeningSet union(WeakeningSet other) {
        if (other == null || other.causes.isEmpty()) {
            return this;
        }
        if (causes.isEmpty()) {
            return other;
        }
        Set<Weakening> both = new LinkedHashSet<>(causes);
        both.addAll(other.causes);
        return new WeakeningSet(both);
    }

    public boolean isEmpty() {
        return causes.isEmpty();
    }

    @Override
    public String toString() {
        return causes.toString();
    }
}
