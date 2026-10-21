package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;

import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.AbstractMap;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.Formatter;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Properties;
import java.util.Set;
import java.util.Vector;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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

    public static List<CompositionBudget> keptByAFunctionOfAStreamAndTakenOut(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = List.of(Set.copyOf(values));
        return new ArrayList<>(holder.stream().map(each -> each).findFirst().orElseThrow());
    }

    public static List<CompositionBudget> keptByAFunctionThatMakesAStream(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = List.of(Set.copyOf(values));
        return new ArrayList<>(holder.stream().flatMap(each -> Stream.of(each)).findFirst()
                .orElseThrow());
    }

    public static List<CompositionBudget> keptByAFunctionOfAnOptional(
            Set<CompositionBudget> values) {
        return new ArrayList<>(Optional.of(Set.copyOf(values)).map(each -> each).orElseThrow());
    }

    public static List<CompositionBudget> putByTheThreeArgumentReplace(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("k", Set.of());
        holder.replace("k", Set.of(), Set.copyOf(values));
        return new ArrayList<>(holder.get("k"));
    }

    public static List<CompositionBudget> putByTheTwoArgumentReplace(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("k", Set.of());
        holder.replace("k", Set.copyOf(values));
        return new ArrayList<>(holder.get("k"));
    }

    /** A vector because inserting an element at an index is a way only it has. */
    @SuppressWarnings("JdkObsolete")
    public static List<CompositionBudget> insertedAtAnIndexOfAVector(
            Set<CompositionBudget> values) {
        Vector<Set<CompositionBudget>> holder = new Vector<>();
        holder.insertElementAt(Set.copyOf(values), 0);
        return new ArrayList<>(holder.firstElement());
    }

    public static List<CompositionBudget> putOnABlockingQueue(Set<CompositionBudget> values)
            throws InterruptedException {
        BlockingQueue<Set<CompositionBudget>> holder = new LinkedBlockingQueue<>();
        holder.put(Set.copyOf(values));
        return new ArrayList<>(holder.take());
    }

    public static List<CompositionBudget> setOnAnEntry(Set<CompositionBudget> values) {
        Map.Entry<String, Set<CompositionBudget>> holder =
                new AbstractMap.SimpleEntry<>("k", Set.of());
        holder.setValue(Set.copyOf(values));
        return new ArrayList<>(holder.getValue());
    }

    public static List<CompositionBudget> theOldValueOfAnEntryThatIsSet(
            Set<CompositionBudget> values) {
        Map.Entry<String, Set<CompositionBudget>> holder =
                new AbstractMap.SimpleEntry<>("k", Set.copyOf(values));
        Set<CompositionBudget> old = holder.setValue(Set.of());
        return new ArrayList<>(old);
    }

    public static List<CompositionBudget> addedThroughAListIterator(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        ListIterator<Set<CompositionBudget>> cursor = holder.listIterator();
        cursor.add(Set.copyOf(values));
        return new ArrayList<>(holder.getFirst());
    }

    public static List<CompositionBudget> setThroughAnEntryOfAMap(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("k", Set.of());
        Map.Entry<String, Set<CompositionBudget>> entry = holder.entrySet().iterator().next();
        entry.setValue(Set.copyOf(values));
        return new ArrayList<>(holder.get("k"));
    }

    public static List<CompositionBudget> concatenatedWithAnEmptyStream(
            Set<CompositionBudget> values) {
        Stream<Set<CompositionBudget>> left = Stream.of(Set.copyOf(values));
        return new ArrayList<>(Stream.concat(left, Stream.empty()).findFirst().orElseThrow());
    }

    @SuppressWarnings("unchecked")
    public static List<CompositionBudget> wrappedByACheckedList(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        List<Set<CompositionBudget>> checked = Collections.checkedList(holder,
                (Class<Set<CompositionBudget>>) (Class<?>) Set.class);
        return new ArrayList<>(checked.getFirst());
    }

    public static List<CompositionBudget> handedBackByRequireNonNull(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return new ArrayList<>(Objects.requireNonNull(holder).getFirst());
    }

    public static String saidAsTheTextOfTheContainer(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return holder.toString();
    }

    /** The array a container is copied into is written, and what is read back is the copy. */
    @SuppressWarnings("unchecked")
    public static List<CompositionBudget> copiedIntoTheArrayItIsGiven(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = List.of(Set.copyOf(values));
        Set<CompositionBudget>[] target = (Set<CompositionBudget>[]) new Set<?>[1];
        if (holder.toArray(target) != target) {
            return List.of();
        }
        return new ArrayList<>(target[0]);
    }

    @SuppressWarnings("unchecked")
    public static List<CompositionBudget> copiedIntoAnArrayItMakes(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = List.of(Set.copyOf(values));
        return new ArrayList<>((Set<CompositionBudget>) Arrays.asList(holder.toArray())
                .getFirst());
    }

    /** A formatter keeps what it is made to say, and says it when it is asked, not when told. */
    public static String saidByAFormatterAskedLater(Set<CompositionBudget> values) {
        Formatter formatter = new Formatter();
        formatter.format("%s", List.of(Set.copyOf(values)));
        return formatter.toString();
    }

    public static String saidByAFormatterAskedByTheCall(Set<CompositionBudget> values) {
        return new Formatter().format("%s", Set.copyOf(values)).toString();
    }

    /** What a formatter says it says into where it was made to write, which is read from there. */
    public static String saidThroughAFormatterOverABuilder(Set<CompositionBudget> values) {
        StringBuilder out = new StringBuilder();
        Formatter formatter = new Formatter(out);
        formatter.format("%s", Set.copyOf(values));
        return out.toString();
    }

    public static void saidThroughAFormatterOverStandardOut(Set<CompositionBudget> values) {
        Formatter formatter = new Formatter(System.out);
        formatter.format("%s", Set.copyOf(values));
    }

    public static String saidThroughAFormatterOverAWriter(Set<CompositionBudget> values) {
        StringWriter out = new StringWriter();
        new Formatter(out).format("%s", Set.copyOf(values));
        return out.toString();
    }

    public static String printedThroughAPrintWriterOverAWriter(Set<CompositionBudget> values) {
        StringWriter out = new StringWriter();
        PrintWriter printer = new PrintWriter(out);
        printer.print(Set.copyOf(values));
        printer.flush();
        return out.toString();
    }

    public static String printedThroughAPrintWriterOverABufferedWriter(
            Set<CompositionBudget> values) {
        StringWriter out = new StringWriter();
        PrintWriter printer = new PrintWriter(new BufferedWriter(out));
        printer.printf("%s", Set.copyOf(values));
        printer.flush();
        return out.toString();
    }

    public static String writtenTextOfTheCopyToAWriter(Set<CompositionBudget> values) {
        StringWriter out = new StringWriter();
        out.write(Set.copyOf(values).toString());
        return out.toString();
    }

    public static String appendedTextOfTheCopyToAnAppendable(Set<CompositionBudget> values) {
        StringBuilder out = new StringBuilder();
        Appendable into = out;
        try {
            into.append(String.valueOf(Set.copyOf(values)));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return out.toString();
    }

    public static String printedThroughAPrintStreamOverABuffer(Set<CompositionBudget> values) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream printer = new PrintStream(out);
        printer.print(Set.copyOf(values));
        printer.flush();
        return out.toString(StandardCharsets.UTF_8);
    }

    /** A writer nothing here made is a window onto wherever whoever made it wrote to. */
    public static void saidThroughAWriterHandedIn(PrintWriter out,
                                                  Set<CompositionBudget> values) {
        out.printf("%s", Set.copyOf(values));
    }

    public static void saidThroughAFormatterHandedIn(Formatter out,
                                                     Set<CompositionBudget> values) {
        out.format("%s", Set.copyOf(values));
    }

    public static void saidThroughAFormatterOverAFile(Set<CompositionBudget> values)
            throws FileNotFoundException {
        try (Formatter out = new Formatter("said.txt")) {
            out.format("%s", Set.copyOf(values));
        }
    }

    public static String saidThroughAFormatterTheTextOfTheCopyWasMadeFor(
            Set<CompositionBudget> values) {
        StringBuilder out = new StringBuilder();
        new Formatter(out).format("%s", String.valueOf(Set.copyOf(values)));
        return out.toString();
    }

    public static String saidThroughAFormatterHandedToAHelper(Set<CompositionBudget> values) {
        StringBuilder out = new StringBuilder();
        saidThroughAFormatterHandedToAHelperSays(new Formatter(out), Set.copyOf(values));
        return out.toString();
    }

    private static void saidThroughAFormatterHandedToAHelperSays(Formatter into,
                                                                 Set<CompositionBudget> copy) {
        into.format("%s", copy);
    }

    public static String saidByObjectsToStringOfTheContainer(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return Objects.toString(holder);
    }

    public static String saidByTheTextOfAnOptional(Set<CompositionBudget> values) {
        return Optional.of(Set.copyOf(values)).toString();
    }

    public static String saidByTheTextOfAMapThatHoldsTheCopyAsAKey(Set<CompositionBudget> values) {
        Map<Set<CompositionBudget>, String> holder = new HashMap<>();
        holder.put(Set.copyOf(values), "k");
        return holder.toString();
    }

    /** What is written is written in the order its text says, whether by a format or by a line. */
    public static void writtenByAPrintf(Set<CompositionBudget> values) {
        System.out.printf("%s", Set.copyOf(values));
    }

    public static void writtenByAPrintlnOfTheContainer(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        System.out.println(holder);
    }

    /** The arguments of a format are handed over as one array, and each is made text. */
    public static String saidByAFormatOfTheCopy(Set<CompositionBudget> values) {
        return String.format("%s", Set.copyOf(values));
    }

    public static String saidByAFormattedOfTheCopy(Set<CompositionBudget> values) {
        return "%s".formatted(Set.copyOf(values));
    }

    public static String saidByAFormatOfAContainerOfTheCopy(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return String.format("%s", holder);
    }

    /** An array inside an array says what it is, unless the text goes down into the arrays. */
    public static String saidByTheDeepTextOfAnArrayInAnArray(Set<CompositionBudget> values) {
        Object[] inner = new Object[1];
        inner[0] = Set.copyOf(values);
        Object[][] outer = new Object[1][];
        outer[0] = inner;
        return Arrays.deepToString(outer);
    }

    @SuppressWarnings("JdkObsolete")
    public static List<CompositionBudget> theValueAHashtableForEachIsGiven(
            Set<CompositionBudget> values) {
        Hashtable<String, Set<CompositionBudget>> holder = new Hashtable<>();
        holder.put("k", Set.copyOf(values));
        List<CompositionBudget> out = new ArrayList<>();
        holder.forEach((_, value) -> out.addAll(value));
        return out;
    }

    @SuppressWarnings({"JdkObsolete", "unchecked"})
    public static List<CompositionBudget> theValueAPropertiesForEachIsGiven(
            Set<CompositionBudget> values) {
        Properties holder = new Properties();
        holder.put("k", Set.copyOf(values));
        List<CompositionBudget> out = new ArrayList<>();
        holder.forEach((_, value) -> out.addAll((Set<CompositionBudget>) value));
        return out;
    }

    public static List<CompositionBudget> addedThroughACursorAHelperIsGiven(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        addedThroughACursorAHelperIsGivenStores(holder.listIterator(), Set.copyOf(values));
        return new ArrayList<>(holder.getFirst());
    }

    private static void addedThroughACursorAHelperIsGivenStores(
            ListIterator<Set<CompositionBudget>> cursor, Set<CompositionBudget> given) {
        cursor.add(given);
    }

    public static List<CompositionBudget> setThroughAnEntryAHelperIsGiven(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("k", Set.of());
        setThroughAnEntryAHelperIsGivenStores(holder.entrySet().iterator().next(),
                Set.copyOf(values));
        return new ArrayList<>(holder.get("k"));
    }

    private static void setThroughAnEntryAHelperIsGivenStores(
            Map.Entry<String, Set<CompositionBudget>> entry, Set<CompositionBudget> given) {
        entry.setValue(given);
    }

    /** Where a cursor comes from is something nothing here reads, and is a view of something. */
    public interface Source {

        ListIterator<Set<CompositionBudget>> cursor();
    }

    public static List<CompositionBudget> addedThroughACursorNothingHereMade(Source source,
                                                                              Set<CompositionBudget> values) {
        source.cursor().add(Set.copyOf(values));
        return new ArrayList<>(source.cursor().next());
    }

    public static List<CompositionBudget> addedThroughASublist(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.subList(0, 0).add(Set.copyOf(values));
        return new ArrayList<>(holder.getFirst());
    }

    /** Unlike the array's own text, this says each element, and an element is a set. */
    public static String saidByTheTextOfTheElementsOfAnArray(Set<CompositionBudget> values) {
        Object[] array = new Object[1];
        array[0] = Set.copyOf(values);
        return Arrays.toString(array);
    }

    public static String saidByTheDeepTextOfTheElementsOfAnArray(Set<CompositionBudget> values) {
        Object[] array = new Object[1];
        array[0] = Set.copyOf(values);
        return Arrays.deepToString(array);
    }

    public static String saidInAConcatenationWithTheContainer(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return "held: " + holder;
    }

    public static String saidByAnAppendOfTheContainer(Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        StringBuilder out = new StringBuilder();
        out.append(holder);
        return out.toString();
    }

    @SuppressWarnings("unchecked")
    public static List<CompositionBudget> addedAllFromAnArrayByTheLibrary(
            Set<CompositionBudget> values) {
        Set<CompositionBudget>[] array = (Set<CompositionBudget>[]) new Set<?>[1];
        array[0] = Set.copyOf(values);
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        Collections.addAll(holder, array);
        return new ArrayList<>(holder.getFirst());
    }

    @SuppressWarnings("unchecked")
    public static List<CompositionBudget> copiedBetweenArraysByTheLibrary(
            Set<CompositionBudget> values) {
        Set<CompositionBudget>[] from = (Set<CompositionBudget>[]) new Set<?>[1];
        Set<CompositionBudget>[] to = (Set<CompositionBudget>[]) new Set<?>[1];
        from[0] = Set.copyOf(values);
        System.arraycopy(from, 0, to, 0, 1);
        return new ArrayList<>(to[0]);
    }

    public static List<CompositionBudget> filledIntoAListByTheLibrary(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>(List.of(Set.of()));
        Collections.fill(holder, Set.copyOf(values));
        return new ArrayList<>(holder.getFirst());
    }

    public static List<CompositionBudget> theOldValueAComputeIsGiven(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("k", Set.copyOf(values));
        List<CompositionBudget> out = new ArrayList<>();
        holder.compute("k", (key, current) -> {
            out.addAll(current);
            return current;
        });
        return out;
    }

    public static List<CompositionBudget> theValueAMapReplaceAllIsGiven(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("k", Set.copyOf(values));
        List<CompositionBudget> out = new ArrayList<>();
        holder.replaceAll((key, current) -> {
            out.addAll(current);
            return current;
        });
        return holder.isEmpty() ? List.of() : out;
    }

    public static List<CompositionBudget> theSecondElementAComparatorIsGiven(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        holder.add(Set.of());
        List<CompositionBudget> out = new ArrayList<>();
        holder.sort((_, second) -> {
            out.addAll(second);
            return 0;
        });
        return holder.isEmpty() ? List.of() : out;
    }

    public static List<CompositionBudget> theElementsAStaticSortGivesItsComparator(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        List<CompositionBudget> out = new ArrayList<>();
        Collections.sort(holder, (first, _) -> {
            out.addAll(first);
            return 0;
        });
        return out;
    }

    public static List<CompositionBudget> madeByTheFunctionOfAMapOverAnotherStream(
            Set<CompositionBudget> values) {
        return new ArrayList<>(Stream.of("x").map(each -> Set.copyOf(values)).findFirst()
                .orElseThrow());
    }

    public static List<CompositionBudget> madeByTheSupplierOfRequireNonNullElseGet(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder =
                Objects.requireNonNullElseGet(null, () -> List.of(Set.copyOf(values)));
        return new ArrayList<>(holder.getFirst());
    }

    public static List<CompositionBudget> madeByTheFunctionOfAComputeIfAbsent(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.computeIfAbsent("k", key -> Set.copyOf(values));
        return new ArrayList<>(holder.get("k"));
    }

    public static List<CompositionBudget> madeByTheFunctionOfAMerge(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder = new HashMap<>();
        holder.put("k", Set.of());
        holder.merge("k", Set.of(), (old, given) -> Set.copyOf(values));
        return new ArrayList<>(holder.get("k"));
    }

    /** What a function returns is a copy, and the call it is handed to is not one this reads. */
    public static List<CompositionBudget> returnedByTheValueFunctionOfACollectorNobodyReads(
            Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> made = Stream.of("x").collect(
                Collectors.toMap(each -> each, each -> Set.copyOf(values)));
        return new ArrayList<>(made.get("x"));
    }

    /** Handed to what nothing says what it does with: said so, and not taken for followed. */
    public static List<CompositionBudget> handedToACollectorNothingFollows(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = new ArrayList<>();
        holder.add(Set.copyOf(values));
        return new ArrayList<>(holder.stream().collect(Collectors.toList()).getFirst());
    }

    public static List<CompositionBudget> heldByASingletonMap(Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder =
                Collections.singletonMap("k", Set.copyOf(values));
        return new ArrayList<>(holder.get("k"));
    }

    public static List<CompositionBudget> heldByCopiesOfOneElement(
            Set<CompositionBudget> values) {
        List<Set<CompositionBudget>> holder = Collections.nCopies(2, Set.copyOf(values));
        return new ArrayList<>(holder.getFirst());
    }

    public static List<CompositionBudget> heldByTheEntriesOfAMap(Set<CompositionBudget> values) {
        Map<String, Set<CompositionBudget>> holder =
                Map.ofEntries(Map.entry("k", Set.copyOf(values)));
        return new ArrayList<>(holder.get("k"));
    }

    @SuppressWarnings("unchecked")
    public static List<CompositionBudget> heldInAnArray(Set<CompositionBudget> values) {
        Set<CompositionBudget>[] holder = (Set<CompositionBudget>[]) new Set<?>[1];
        holder[0] = Set.copyOf(values);
        return new ArrayList<>(holder[0]);
    }

    public static List<CompositionBudget> heldByAListMadeOfAnArray(Set<CompositionBudget> values) {
        @SuppressWarnings("unchecked")
        Set<CompositionBudget>[] holder = (Set<CompositionBudget>[]) new Set<?>[1];
        holder[0] = Set.copyOf(values);
        return new ArrayList<>(Arrays.asList(holder).getFirst());
    }

    /** Wrapped as often as there are levels, which is a number the reading does not know. */
    @SuppressWarnings("unchecked")
    public static List<CompositionBudget> wrappedInAListAsOftenAsAskedAndTakenOut(
            Set<CompositionBudget> values, int levels) {
        Object holder = Set.copyOf(values);
        for (int each = 0; each < levels; each++) {
            holder = List.of(holder);
        }
        for (int each = 0; each < levels; each++) {
            holder = ((List<Object>) holder).getFirst();
        }
        return new ArrayList<>((Set<CompositionBudget>) holder);
    }

    public static List<CompositionBudget> wrappedByARecursionAndTakenOut(
            Set<CompositionBudget> values, int levels) {
        return new ArrayList<>(unwrapped(wrapped(Set.copyOf(values), levels), levels));
    }

    private static Object wrapped(Object inner, int levels) {
        return levels == 0 ? inner : wrapped(List.of(inner), levels - 1);
    }

    @SuppressWarnings("unchecked")
    private static Set<CompositionBudget> unwrapped(Object outer, int levels) {
        return levels == 0 ? (Set<CompositionBudget>) outer
                : unwrapped(((List<Object>) outer).getFirst(), levels - 1);
    }

    public static List<CompositionBudget> heldAsAKeyAndTakenOutOfTheKeys(
            Set<CompositionBudget> values) {
        Map<Set<CompositionBudget>, String> holder = new HashMap<>();
        holder.put(Set.copyOf(values), "figures");
        return new ArrayList<>(holder.keySet().iterator().next());
    }
}
