package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Readers that make a copy, hold it whole in a container, and take its order into an answer after
 * taking it out again, one way apiece.
 *
 * <p>Every public method is one the walk must refuse, and for the copy that method makes itself
 * and no other: the container's own order is nobody's, so an answer that names a copy the method
 * never made has followed the wrong thing. A helper's name begins with the name of the method that
 * hands it the container.
 */
public final class HeldWholeAndTakenOut {

    private HeldWholeAndTakenOut() {}

    public static List<CompositionBudget> inAListAndTakenFirst(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return new ArrayList<>(holder.getFirst());
    }

    public static List<CompositionBudget> asAMapValue(Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("figures", Set.copyOf(values));
        return new ArrayList<>(holder.get("figures"));
    }

    public static List<CompositionBudget> inAListMadeByTheFactory(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = List.of(Set.copyOf(values));
        return new ArrayList<>(holder.getFirst());
    }

    public static List<CompositionBudget> handedToAHelper(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return handedToAHelperTakesItOut(holder);
    }

    private static List<CompositionBudget> handedToAHelperTakesItOut(
            List<Set<CompositionBudget>> holder) {
        return new ArrayList<>(holder.getFirst());
    }

    public static List<CompositionBudget> takenOffTheFrontOfAQueue(
            Set<CompositionBudget> values) {
        Deque<Set<CompositionBudget>> holder = new ArrayDeque<>();
        holder.add(Set.copyOf(values));
        return new ArrayList<>(holder.removeFirst());
    }

    public static List<CompositionBudget> takenByAStreamOverTheValues(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("figures", Set.copyOf(values));
        return new ArrayList<>(holder.values().stream().findFirst().orElseThrow());
    }

    public static List<CompositionBudget> takenOutOfAListInAList(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> inner = new ArrayList<>();
        inner.add(Set.copyOf(values));
        List<List<Set<CompositionBudget>>> outer = new ArrayList<>();
        outer.add(inner);
        return new ArrayList<>(outer.getFirst().getFirst());
    }

    public static List<CompositionBudget> heldInAListCopiedByAddAll(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> first = new ArrayList<>();
        first.add(Set.copyOf(values));
        List<Set<CompositionBudget>> second = new ArrayList<>();
        second.addAll(first);
        return new ArrayList<>(second.getFirst());
    }

    public static List<CompositionBudget> heldInAListCopiedByAConstructor(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> first = new ArrayList<>();
        first.add(Set.copyOf(values));
        List<Set<CompositionBudget>> second = new ArrayList<>(first);
        return new ArrayList<>(second.getFirst());
    }

    public static List<CompositionBudget> takenOutByAForEach(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        List<CompositionBudget> out = new ArrayList<>();
        for (Set<CompositionBudget> each : holder) {
            out.addAll(each);
        }
        return out;
    }

    public static List<CompositionBudget> takenOutOfAnEntry(Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("figures", Set.copyOf(values));
        List<CompositionBudget> out = new ArrayList<>();
        for (Map.Entry<String, Set<CompositionBudget>> each : holder.entrySet()) {
            out.addAll(each.getValue());
        }
        return out;
    }

    @SuppressWarnings("unchecked")
    public static List<CompositionBudget> heldBesideTheElementsOfAnotherCopy(
            Set<CompositionBudget> one, Set<CompositionBudget> other) {
        List<Object> holder = new ArrayList<>();
        holder.add(Set.copyOf(one));
        holder.addAll(Set.copyOf(other));
        return new ArrayList<>((Set<CompositionBudget>) holder.getFirst());
    }

    public static List<CompositionBudget> heldAsAKeyAndTakenOutOfTheKeys(
            Set<CompositionBudget> values) {
        Map<Set<CompositionBudget>, String> holder = new HashMap<>();
        holder.put(Set.copyOf(values), "figures");
        return new ArrayList<>(holder.keySet().iterator().next());
    }
}
