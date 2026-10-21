package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Readers that hold a copy whole and then put something else where it was, which the reading
 * reads as holding both.
 *
 * <p>What a container carries is the paths a copy is held at, and not the keys of a map or the
 * positions of a list, so a put to a key a copy was put to does not take the copy out. Each reader
 * here returns an order that is the second thing's, and is named for the copy all the same. A reading
 * that tells the two apart makes these readers pass, and the test that holds them to this is the one
 * that says so.
 */
public final class HeldWholeAndOverwritten {

    private HeldWholeAndOverwritten() {}

    public static List<CompositionBudget> putAgainUnderTheSameKey(Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("k", Set.copyOf(values));
        holder.put("k", new LinkedHashSet<>());
        return new ArrayList<>(holder.get("k"));
    }

    public static List<CompositionBudget> setAtTheSamePositionAgain(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        holder.set(0, new LinkedHashSet<>());
        return new ArrayList<>(holder.getFirst());
    }
}
