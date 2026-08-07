package souther.compiler.partition;

import souther.compiler.types.Type;

import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * One input position that a model distinguishes values at, and the classes it distinguishes them into.
 *
 * <p>The model's own distinctions, not invented ones. A type with two cases has two classes; a newtype
 * whose invariant bounds it has a class on each side of the bound. A position the model says nothing
 * about — a plain {@code String}, an {@code Int} with no invariant — has no classes, and that is
 * reported as not derivable rather than filled in with values nobody asked for. The choice matters:
 * a made-up partition measures a rule the model does not have, and reports coverage of it.
 *
 * @param classes  exclusive and exhaustive over the position's values, or empty where the model does
 *                 not divide them
 * @param cuts     the values the classes meet at, each carrying every rule that drew it there
 * @param excluded the ids of the classes the body says it does not answer for. Still classes — the
 *                 position's values are still divided this way, and a report says so — and not ones a
 *                 row can be written at, since reaching one is E1911
 */
public record Axis(AxisId id, TermPath path, Type type, List<PartitionClass> classes,
                   List<Cut> cuts, Set<String> excluded) {

    public Axis {
        classes = List.copyOf(classes);
        cuts = List.copyOf(cuts);
        excluded = Set.copyOf(excluded);
    }

    public Axis(AxisId id, TermPath path, Type type, List<PartitionClass> classes, List<Cut> cuts) {
        this(id, path, type, classes, cuts, Set.of());
    }

    /** A position the model does not divide. Kept, so a report can name what it could not measure. */
    public static Axis notDerivable(AxisId id, TermPath path, Type type) {
        return new Axis(id, path, type, List.of(), List.of());
    }

    /** The same position, with what the body rules out marked.
     *
     * <p>An id this axis has no class for is dropped rather than kept: what a behavior's body says
     * about one position cannot make a class appear at another, and an exclusion is matched within
     * the axis it belongs to because a class id is unique there and nowhere wider. */
    public Axis excluding(Collection<String> ids) {
        Set<String> here = ids.stream().filter(id -> classOf(id) != null)
                .collect(java.util.stream.Collectors.toCollection(java.util.LinkedHashSet::new));
        return here.isEmpty() ? this : new Axis(id, path, type, classes, cuts, here);
    }

    /**
     * The classes a row can be written at.
     *
     * <p>The one denominator. What a report counts, what a pair space is the product of, and what the
     * generator offers rows for all come from here — three derivations of the same universe are three
     * chances to disagree about it, which is how a class nothing can reach came to be asked for by
     * three measures at once.
     */
    public List<PartitionClass> eligible() {
        return classes.stream().filter(each -> !excluded.contains(each.id())).toList();
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
