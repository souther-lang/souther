package souther.bench;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.TypeVariable;
import java.util.AbstractMap;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.NavigableMap;
import java.util.NavigableSet;
import java.util.Optional;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.SequencedCollection;
import java.util.SequencedMap;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Vector;
import java.util.concurrent.BlockingDeque;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.LinkedBlockingDeque;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a method of the library's collections stores, or hands back from what it holds, is a row of
 * the table of held copies, or is said not to be one and why.
 *
 * <p>The table names an operation by its name and the number of arguments it is given, and the
 * value it stores stands where that pair says: a table written from the operations somebody
 * thought of is as long as their list. So the table is put to the library instead. Every method of
 * these classes whose name is a way of putting something in is a row, or is a way that stores no
 * element, and every method that answers a type variable — which is an element, a key or a value
 * the collection held — is a way of taking one out, or is not one and says why. A method added to
 * the library, or a class added here, fails until it is read.
 */
class EveryOperationOfTheCollectionsThatStoresOrTakesIsInTheHeldCopiesTableTest {

    private static final Pattern PUTS_SOMETHING_IN = Pattern.compile(
            "^(add|put|offer|push|set|replace|insert|merge|compute|append).*");

    /** The ways of putting in that store no element or key or value of the collection's. */
    private static final Map<String, String> STORES_NO_ELEMENT = Map.of(
            "setSize", "a size, which pads with nothing",
            "setLength", "a length, which pads with nothing",
            "setDefault", "a default of the iteration, which is not held");

    /** What answers a type variable and is not one of the collection's own. */
    private static final Map<String, String> ANSWERS_NO_ELEMENT = Map.of(
            "search", "answers what a function it is given returns, which is not followed",
            "searchKeys", "answers what a function it is given returns, which is not followed",
            "searchValues", "answers what a function it is given returns, which is not followed",
            "searchEntries", "answers what a function it is given returns, which is not followed",
            "reduceKeys", "answers what a function it is given returns, which is not followed",
            "reduceValues", "answers what a function it is given returns, which is not followed",
            "reduceEntries", "answers what a function it is given returns, which is not followed");

    /** What a method does that neither reveals nor keeps a copy a container holds, said by name. */
    private static final Map<String, String> NOT_AN_OPERATION_ON_WHAT_IS_HELD = Map.of();

    private static final List<Class<?>> COLLECTIONS = List.of(
            Collection.class, List.class, Deque.class, Queue.class, BlockingQueue.class,
            BlockingDeque.class, SequencedCollection.class, Set.class, SortedSet.class,
            NavigableSet.class, Map.class, SequencedMap.class, SortedMap.class,
            NavigableMap.class, ConcurrentMap.class, Vector.class, Stack.class, ArrayList.class,
            LinkedList.class, ArrayDeque.class, PriorityQueue.class, HashMap.class,
            LinkedHashMap.class, TreeMap.class, TreeSet.class, Hashtable.class,
            ConcurrentHashMap.class, CopyOnWriteArrayList.class, LinkedBlockingQueue.class,
            LinkedBlockingDeque.class, ListIterator.class, Iterator.class, Enumeration.class,
            Map.Entry.class, AbstractMap.SimpleEntry.class, Optional.class);

    @Test
    void everyWayOfPuttingSomethingInIsARowOrStoresNoElement() {
        List<String> unread = new ArrayList<>();
        for (Method each : methods()) {
            if (!PUTS_SOMETHING_IN.matcher(each.getName()).matches()) {
                continue;
            }
            String name = each.getName();
            boolean read = HeldCopies.placementOf(name, each.getParameterCount()).isPresent()
                    || HeldCopies.putsAllIn(name)
                    || HeldCopies.storesWhatAFunctionMakes(name)
                    || STORES_NO_ELEMENT.containsKey(name);
            if (!read) {
                unread.add(describe(each));
            }
        }

        assertEquals(List.of(), unread.stream().distinct().sorted().toList(),
                "a way of putting something into a collection is not in the table of held copies,"
                        + " so a copy put in that way is not seen to be held");
    }

    @Test
    void everyMethodThatAnswersWhatACollectionHeldIsAWayOfTakingOneOut() {
        List<String> unread = new ArrayList<>();
        for (Method each : methods()) {
            boolean answersAnElement = each.getGenericReturnType() instanceof TypeVariable<?>
                    || Map.Entry.class.equals(each.getReturnType());
            if (answersAnElement && !HeldCopies.takesOut(each.getName())
                    && !ANSWERS_NO_ELEMENT.containsKey(each.getName())) {
                unread.add(describe(each));
            }
        }

        assertEquals(List.of(), unread.stream().distinct().sorted().toList(),
                "a method answers what a collection held and is not in the table of held copies,"
                        + " so a copy taken out in that way is not seen to be the copy");
    }

    /**
     * An operation that stores and answers what it replaced is both: the entry's {@code setValue}
     * puts the new value in and hands the old one back, and a table that read only the first
     * would lose the copy that was there.
     */
    @Test
    void anOperationThatStoresAndAnswersTheValueItReplacedIsAWayOfTakingOneOutToo() {
        List<String> only = new ArrayList<>();
        for (Method each : methods()) {
            boolean stores = HeldCopies.placementOf(each.getName(), each.getParameterCount())
                    .isPresent();
            boolean answersWhatWasThere = each.getGenericReturnType() instanceof TypeVariable<?>;
            if (stores && answersWhatWasThere && !HeldCopies.takesOut(each.getName())) {
                only.add(describe(each));
            }
        }

        assertEquals(List.of(), only.stream().distinct().sorted().toList(),
                "an operation stores a value and answers the one it replaced, and is read as"
                        + " storing only");
    }

    /**
     * Every method of these collections is one the reading of held copies has a word for: it
     * stores, takes out, makes a view or a copy, clears, asks only what is held, or makes text; or
     * it is listed here with what it does that nothing of the above says.
     */
    @Test
    void everyMethodOfTheCollectionsIsOneTheReadingOfHeldCopiesHasAWordFor() {
        List<String> unread = new ArrayList<>();
        for (Method each : methods()) {
            if (!HeldCopies.understands(each.getName(), each.getParameterCount())
                    && !NOT_AN_OPERATION_ON_WHAT_IS_HELD.containsKey(each.getName())) {
                unread.add(describe(each));
            }
        }

        assertEquals(List.of(), unread.stream().distinct().sorted().toList(),
                "a method of the collections is not one the reading of held copies knows: a"
                        + " container that holds a copy and is handed to it is said not to be"
                        + " followed, so say here what it does, or read it");
    }

    /**
     * The order reading and the table of held copies agree on what puts something in: a name the
     * first calls a put is a row of the second, or is text. Two lists of the same thing are two
     * answers, and an operation in one only is read as a put by one of them and as nothing by
     * the other.
     */
    @Test
    void theOrderReadingCallsNothingAPutThatTheTableOfHeldCopiesDoesNotStore() {
        Set<String> text = Set.of("append", "insert");
        List<String> only = new ArrayList<>();
        for (String name : SaltedOrderVocabulary.namesThatPutOneIn()) {
            boolean row = false;
            for (int arity = 0; arity <= 4; arity++) {
                row |= HeldCopies.placementOf(name, arity).isPresent();
            }
            if (!row && !text.contains(name)) {
                only.add(name);
            }
        }

        assertEquals(List.of(), only.stream().sorted().toList(),
                "the order reading calls a name a put and the table of held copies has no row");
    }

    /** The control: the tables hold the cases that are known to be easy to get wrong. */
    @Test
    void theValueAnOperationStoresIsWhereItsArgumentsPutIt() {
        assertEquals(new HeldCopies.Placement(0, 1),
                HeldCopies.placementOf("replace", 2).orElseThrow());
        assertEquals(new HeldCopies.Placement(0, 2),
                HeldCopies.placementOf("replace", 3).orElseThrow());
        assertEquals(new HeldCopies.Placement(HeldCopies.Placement.NONE, 0),
                HeldCopies.placementOf("insertElementAt", 2).orElseThrow());
        assertEquals(new HeldCopies.Placement(HeldCopies.Placement.NONE, 0),
                HeldCopies.placementOf("put", 1).orElseThrow());
        assertEquals(new HeldCopies.Placement(HeldCopies.Placement.NONE, 1),
                HeldCopies.placementOf("add", 2).orElseThrow());
        assertEquals(new HeldCopies.Placement(HeldCopies.Placement.NONE, 0),
                HeldCopies.placementOf("offer", 3).orElseThrow());
        assertTrue(HeldCopies.placementOf("replace", 4).isEmpty(),
                "an operation that no method of the library has was given a place");
    }

    /** The control: the sweep reads the collections of the library and is not empty. */
    @Test
    void theSweepReadsMethodsOfEveryKindItAsksAbout() {
        assertFalse(methods().isEmpty(), "no method was read");
        assertTrue(methods().stream().anyMatch(each ->
                        PUTS_SOMETHING_IN.matcher(each.getName()).matches()),
                "no way of putting something in was read");
        assertTrue(methods().stream().anyMatch(each ->
                        each.getGenericReturnType() instanceof TypeVariable<?>),
                "no method answering an element was read");
    }

    private static List<Method> methods() {
        List<Method> out = new ArrayList<>();
        for (Class<?> each : COLLECTIONS) {
            for (Method method : each.getMethods()) {
                if (!Modifier.isStatic(method.getModifiers())
                        && !method.getDeclaringClass().equals(Object.class)) {
                    out.add(method);
                }
            }
        }
        return out;
    }

    private static String describe(Method method) {
        return method.getDeclaringClass().getSimpleName() + "." + method.getName() + "/"
                + method.getParameterCount();
    }
}
