package souther.compiler.check;

import souther.compiler.types.ConstructOccurrence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The departures of each attempted construction a body makes that the discharge check found no run
 * takes, by the copy of the attempt they are of.
 *
 * <p>The check's answer and not a second reading of one. It reads the tree where the language's
 * operations stand, which says more of what they answer than the tree that runs, so a reader of the
 * other tree asking whether a departure is entered asks this as well ({@link PathReachability}).
 *
 * <p>Every reading the check made of one copy, together: a body read once per arm of a split above
 * the attempt is read over each arm's runs, and a departure is one no run takes where every reading
 * found so. A copy the check made no reading of is not here, which says nothing of it.
 *
 * @param byAttempt for each copy of an attempt, each of its departures in the order they are
 *                  written, as whether no run takes it
 */
public record DeparturesNoRunTakes(Map<ConstructOccurrence, List<Boolean>> byAttempt) {

    /** Nothing found, which is what a body the check did not finish reading has. */
    public static final DeparturesNoRunTakes NONE = new DeparturesNoRunTakes(Map.of());

    public DeparturesNoRunTakes {
        Map<ConstructOccurrence, List<Boolean>> copy = new LinkedHashMap<>();
        byAttempt.forEach((attempt, each) -> copy.put(attempt, List.copyOf(each)));
        byAttempt = Collections.unmodifiableMap(copy);
    }

    /** Whether the check found no run takes departure {@code index} of the copy {@code attempt}. */
    public boolean shut(ConstructOccurrence attempt, int index) {
        List<Boolean> each = byAttempt.get(attempt);
        return each != null && index < each.size() && each.get(index);
    }

    /** What two readings of one copy found together: a departure no run takes where both found
     *  so. */
    static List<Boolean> together(List<Boolean> one, List<Boolean> other) {
        List<Boolean> both = new ArrayList<>();
        for (int i = 0; i < one.size(); i++) {
            both.add(one.get(i) && i < other.size() && other.get(i));
        }
        return both;
    }
}
