package souther.compiler.partition;

import souther.compiler.types.Type;

import java.util.List;

/**
 * One input position that a model distinguishes values at, and the classes it distinguishes them into.
 *
 * <p>The model's own distinctions, not invented ones. A type with two cases has two classes; a newtype
 * whose invariant bounds it has a class on each side of the bound. A position the model says nothing
 * about — a plain {@code String}, an {@code Int} with no invariant — has no classes, and that is
 * reported as not derivable rather than filled in with values nobody asked for. The choice matters:
 * a made-up partition measures a rule the model does not have, and reports coverage of it.
 *
 * @param classes exclusive and exhaustive over the position's values, or empty where the model does
 *                not divide them
 * @param cuts    the values the classes meet at, each carrying every rule that drew it there
 */
public record Axis(AxisId id, TermPath path, Type type, List<PartitionClass> classes,
                   List<Cut> cuts) {

    public Axis {
        classes = List.copyOf(classes);
        cuts = List.copyOf(cuts);
    }

    /** A position the model does not divide. Kept, so a report can name what it could not measure. */
    public static Axis notDerivable(AxisId id, TermPath path, Type type) {
        return new Axis(id, path, type, List.of(), List.of());
    }

    /** Whether the model divides this position into classes to cover. */
    public boolean derivable() {
        return !classes.isEmpty();
    }

    /** Whether there is anything here to measure at all — classes to cover, or a boundary to reach.
     * A numeric newtype bounded by an invariant has the second and not the first: everything outside
     * the bound is refused at construction, so there is no other class, only an edge worth a row. */
    public boolean measurable() {
        return !classes.isEmpty() || !cuts.isEmpty();
    }

    public PartitionClass classOf(String id) {
        return classes.stream().filter(c -> c.id().equals(id)).findFirst().orElse(null);
    }
}
