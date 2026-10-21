package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;
import souther.compiler.publish.PublicationOrders;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * Readers that hold a copy whole in a container and put nothing of its order in an answer.
 *
 * <p>Every public method is one the walk must pass. Each holds a copy the way a reader that is
 * refused does, and differs in what is taken out of the container, or in whether what is taken out
 * is the copy at all.
 */
public final class HeldWholeAndNotTakenOut {

    private HeldWholeAndNotTakenOut() {}

    public static boolean onlyAskedWhatTheCopyTakenOutHolds(Set<CompositionBudget> values,
                                                            CompositionBudget one) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return holder.getFirst().contains(one) && holder.getFirst().size() > 1;
    }

    public static int onlyTheOuterListIsWalked(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        int total = 0;
        for (Set<CompositionBudget> each : holder) {
            total += each.size();
        }
        return total;
    }

    public static List<String> theKeysOfAMapWhoseValuesAreCopies(Set<CompositionBudget> values) {
        Set<String> key = new LinkedHashSet<>(List.of("a", "b"));
        Map<Set<String>, Set<CompositionBudget>> holder = new LinkedHashMap<>();
        holder.put(key, Set.copyOf(values));
        return new ArrayList<>(holder.keySet().iterator().next());
    }

    public static List<CompositionBudget> theValuesOfAMapWhoseKeysAreCopies(
            Set<CompositionBudget> values) {
        List<CompositionBudget> ordered = new ArrayList<>(List.of());
        Map<Set<CompositionBudget>, List<CompositionBudget>> holder = new LinkedHashMap<>();
        holder.put(Set.copyOf(values), ordered);
        return new ArrayList<>(holder.values().iterator().next());
    }

    public static List<CompositionBudget> theKeyOfAnEntryWhoseValueIsTheCopy(
            Set<CompositionBudget> values) {
        List<CompositionBudget> ordered = new ArrayList<>();
        Map<List<CompositionBudget>, Set<CompositionBudget>> holder = new LinkedHashMap<>();
        holder.put(ordered, Set.copyOf(values));
        List<CompositionBudget> out = new ArrayList<>();
        for (Map.Entry<List<CompositionBudget>, Set<CompositionBudget>> each
                : holder.entrySet()) {
            out.addAll(each.getKey());
        }
        return out;
    }

    public static List<CompositionBudget> aCopyThatWasClearedOutBeforeAnOrderedSetWasPut(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        holder.clear();
        holder.add(new LinkedHashSet<>(List.of()));
        return new ArrayList<>(holder.getFirst());
    }

    public static List<Integer> aFunctionOfTheCopiesThatIsNotAnyOfThem(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return holder.stream().map(Set::size).toList();
    }

    public static int onlyTheContainerIsAsked(Set<CompositionBudget> values,
                                              Set<CompositionBudget> other) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        int asked = holder.size() + holder.indexOf(other) + holder.hashCode();
        if (holder.isEmpty() || holder.contains(other) || Objects.isNull(holder)
                || holder.equals(List.of(other))) {
            asked++;
        }
        return asked;
    }

    public static List<CompositionBudget> theOldValueOfAnEntryWasNotTheCopy(
            Set<CompositionBudget> values) {
        Map.Entry<String, Set<CompositionBudget>> holder =
                new AbstractMap.SimpleEntry<>("k", new LinkedHashSet<>());
        Set<CompositionBudget> old = holder.setValue(Set.copyOf(values));
        return new ArrayList<>(old);
    }

    public static List<CompositionBudget> aReplaceWhoseExpectedValueIsTheCopy(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new LinkedHashMap<>();
        holder.put("k", Set.of());
        holder.replace("k", Set.copyOf(values), new LinkedHashSet<>());
        return new ArrayList<>(holder.get("k"));
    }

    public static List<CompositionBudget> putInAnOrderWhenTakenOut(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return PublicationOrders.COMPOSITION_BUDGETS.keep(holder.getFirst()).written();
    }

    public static List<Set<CompositionBudget>> aListOfCopiesCopiedWholeNotWalked(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> inner = new ArrayList<>();
        inner.add(Set.copyOf(values));
        List<List<Set<CompositionBudget>>> outer = new ArrayList<>();
        outer.add(inner);
        return new ArrayList<>(outer.getFirst());
    }
}
