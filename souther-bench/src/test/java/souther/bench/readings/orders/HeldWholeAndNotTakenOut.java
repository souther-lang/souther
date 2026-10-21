package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;
import souther.compiler.publish.PublicationOrders;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Stream;

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

    /** An array says what it is and not what it holds, which is the point of asking it. */
    @SuppressWarnings("ArrayToString")
    public static String theTextOfAnArrayThatHoldsACopy(Set<CompositionBudget> values) {
        Object[] array = new Object[1];
        array[0] = Set.copyOf(values);
        return array.toString() + array;
    }

    /** A stream and a cursor name themselves too, which is the point of asking for their text. */
    @SuppressWarnings({"StreamToString", "UnnecessaryStringBuilder"})
    public static String theTextOfAStreamThatHoldsACopy(Set<CompositionBudget> values) {
        Stream<Set<CompositionBudget>> stream = Stream.of(Set.copyOf(values));
        return new StringBuilder().append(stream).toString();
    }

    public static String theTextOfACursorOverACopy(Set<CompositionBudget> values) {
        Iterator<Set<CompositionBudget>> cursor = List.of(Set.copyOf(values)).iterator();
        return "cursor: " + cursor + String.valueOf(cursor);
    }

    /** The identity of an object is its class and a number, and says nothing of what it holds. */
    public static String theIdentityOfAContainerThatHoldsACopy(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return Objects.toIdentityString(holder);
    }

    /** The text of an array in an array is the inner array's name, and the shallow text stops. */
    public static String theShallowTextOfAnArrayInAnArray(Set<CompositionBudget> values) {
        Object[] inner = new Object[1];
        inner[0] = Set.copyOf(values);
        Object[][] outer = new Object[1][];
        outer[0] = inner;
        return Arrays.toString(outer);
    }

    /** What is handed to a helper keeps what it is: the text of an array or a stream is its name. */
    @SuppressWarnings({"ArrayToString", "StreamToString"})
    public static String theTextOfWhatAHelperIsHanded(Set<CompositionBudget> values) {
        Object[] array = new Object[1];
        array[0] = Set.copyOf(values);
        return theTextOfWhatAHelperIsHandedSaysAStream(Stream.of(Set.copyOf(values)))
                + theTextOfWhatAHelperIsHandedSaysAnArray(array);
    }

    @SuppressWarnings("StreamToString")
    private static String theTextOfWhatAHelperIsHandedSaysAStream(
            Stream<Set<CompositionBudget>> stream) {
        return String.valueOf(stream) + stream;
    }

    @SuppressWarnings("ArrayToString")
    private static String theTextOfWhatAHelperIsHandedSaysAnArray(Object[] array) {
        return String.valueOf(array) + array;
    }

    /** A copy given to a cursor and nothing else is asked of: no put reaches what is held. */
    public static int aCursorOnlyAskedWhereItIs(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        ListIterator<Set<CompositionBudget>> cursor = holder.listIterator();
        return cursor.nextIndex() + (cursor.hasNext() ? 1 : 0);
    }

    public static List<String> aComputeWhoseFunctionIsGivenOnlyTheKey(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new LinkedHashMap<>();
        holder.put("k", Set.copyOf(values));
        List<String> keys = new ArrayList<>();
        holder.compute("k", (key, current) -> {
            keys.add(key);
            return current;
        });
        return keys;
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
