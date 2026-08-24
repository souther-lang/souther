package souther.compiler.inputs;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What has to be true of a value for a position to exist in it, or for a class to hold there.
 *
 * <p>Read off a path and never kept beside one. {@code query@GlobalQuery.tag} says that
 * {@code query} is a {@code GlobalQuery} and says it completely; a position carrying that fact a
 * second time would be two accounts of one thing, waiting to disagree.
 *
 * <p><b>One merge decides every compatibility.</b> Whether two classes can be asked for in one row,
 * whether a pair of them is a combination the model has at all, and what a value being built has to
 * be are the same question asked by three readers. Answered separately, each would work out for
 * itself that a row cannot be a {@code FeedQuery} and have a {@code GlobalQuery}'s {@code tag} — and
 * the coverage denominator and the generator disagreeing about which combinations exist is how a
 * report comes to ask for rows nothing can write.
 */
public record Requirements(Map<TermPath, Refinement> refinements) {

    /** Nothing has to be true: a position under no refinement, or a class that selects none. */
    public static final Requirements NONE = new Requirements(Map.of());

    public Requirements {
        // The order they were reached in, outermost first, which is the order a reason about them
        // reads in.
        refinements = java.util.Collections.unmodifiableMap(new LinkedHashMap<>(refinements));
    }

    /** The same, with {@code refinement} required at {@code at} — which is what a class selecting
     *  one adds to what its position's path already required. */
    public Requirements and(TermPath at, Refinement refinement) {
        if (refinement == null) {
            return this;
        }
        Map<TermPath, Refinement> wider = new LinkedHashMap<>(refinements);
        wider.put(at, refinement);
        return new Requirements(wider);
    }

    /** What is required at {@code at}, or null where nothing is. */
    public Refinement at(TermPath at) {
        return refinements.get(at);
    }

    /**
     * Both, or the position they disagree about.
     *
     * <p>Two requirements are compatible exactly when no position is required to be two different
     * things. A position one of them says nothing about is one the other settles alone: a row is
     * free to be whatever it likes where nothing asked.
     */
    public Merge merge(Requirements other) {
        Map<TermPath, Refinement> both = new LinkedHashMap<>(refinements);
        for (Map.Entry<TermPath, Refinement> each : other.refinements.entrySet()) {
            Refinement had = both.putIfAbsent(each.getKey(), each.getValue());
            if (had != null && !had.equals(each.getValue())) {
                return new Merge.Conflict(each.getKey(), had, each.getValue());
            }
        }
        return new Merge.Merged(new Requirements(both));
    }

    /** Whether the two can hold of one value. */
    public boolean compatibleWith(Requirements other) {
        return merge(other) instanceof Merge.Merged;
    }

    /** What came of putting two requirements together. */
    public sealed interface Merge {

        /** They hold together, and this is what holds. */
        record Merged(Requirements requirements) implements Merge {}

        /**
         * They do not, and this is the position that cannot be both.
         *
         * <p>Which position, and which two, because that is what a report of an absent combination
         * is about: a pair left out of the denominator is left out for a reason an author can read.
         */
        record Conflict(TermPath at, Refinement one, Refinement other) implements Merge {}
    }
}
