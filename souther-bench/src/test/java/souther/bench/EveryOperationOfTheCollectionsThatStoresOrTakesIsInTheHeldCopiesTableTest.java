package souther.bench;

import org.junit.jupiter.api.Test;

import java.io.BufferedOutputStream;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.CharArrayWriter;
import java.io.DataOutputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.ObjectOutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.invoke.MethodType;
import java.lang.reflect.Constructor;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;
import java.lang.reflect.WildcardType;
import java.text.MessageFormat;
import java.util.AbstractMap;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Objects;
import java.util.Deque;
import java.util.Enumeration;
import java.util.Formatter;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Locale;
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
import java.util.stream.BaseStream;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;
import java.util.zip.GZIPOutputStream;

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

    /**
     * The methods that are given a function and are not followed. A container that holds a copy,
     * handed to one, is said so; so is a function that returns a copy and is handed to one.
     */
    private static final Map<String, String> NOT_FOLLOWED_THOUGH_GIVEN_A_FUNCTION =
            notFollowed();

    /**
     * Methods that only some of the JDKs this is built on have. What the sweep reads is the library
     * it runs on, so a method a newer one added fails until it is listed, and one listed here is not
     * required of an older one.
     */
    private static final Set<String> IN_NEWER_JDKS_ONLY = Set.of("ofLazy");

    private static Map<String, String> notFollowed() {
        Map<String, String> out = new TreeMap<>();
        String bulk = "a bulk operation of a concurrent map, which runs a function over entries in"
                + " parallel and answers what a function returns";
        for (String name : List.of("forEach", "forEachEntry", "forEachKey", "forEachValue",
                "reduceEntries", "reduceKeys", "reduceValues", "search", "searchEntries",
                "searchKeys", "searchValues", "reduceEntriesToDouble", "reduceEntriesToInt",
                "reduceEntriesToLong", "reduceKeysToDouble", "reduceKeysToInt",
                "reduceKeysToLong", "reduceToDouble", "reduceToInt", "reduceToLong",
                "reduceValuesToDouble", "reduceValuesToInt", "reduceValuesToLong")) {
            out.put(name, bulk);
        }
        String primitive = "makes numbers of the elements, which are no copy";
        for (String name : List.of("mapToInt", "mapToLong", "mapToDouble", "flatMapToInt",
                "flatMapToLong", "flatMapToDouble")) {
            out.put(name, primitive);
        }
        out.put("collect", "gathers by a collector, which is a value and not a function run here");
        out.put("mapMulti", "hands the elements to a consumer that decides what goes on");
        out.put("iterate", "makes elements of what a function returns of the last one");
        out.put("toArray", "makes an array by a function of its size");
        out.put("requireNonNull", "a message is made by the function, which is text");
        out.put("orElseThrow", "makes the exception thrown, which is no copy");
        out.put("parallelSort", "orders by a comparator, as sort does, in parallel");
        out.put("parallelPrefix", "folds neighbours of an array by a function");
        out.put("parallelSetAll", "sets an array by a function of the index");
        String compares = "compares the elements of arrays by a comparator and answers a number, or"
                + " makes a comparator, and says nothing of where an element goes";
        for (String name : List.of("binarySearch", "compare", "equals", "mismatch",
                "reverseOrder", "comparingByKey", "comparingByValue")) {
            out.put(name, compares);
        }
        out.put("ofLazy", "makes a collection whose elements a function computes when asked");
        out.put("onClose", "runs a handler when a stream is closed, which is given nothing");
        for (String name : List.of("mapMultiToInt", "mapMultiToLong", "mapMultiToDouble")) {
            out.put(name, primitive);
        }
        out.put("reduce", bulk + "; or a fold of three arguments, whose combiner is given the"
                + " partial results of parallel folds");
        return out;
    }

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
                    || HeldCopies.hasACallback(name, each.getParameterCount())
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
                    && !NOT_AN_OPERATION_ON_WHAT_IS_HELD.containsKey(each.getName())
                    && !NOT_FOLLOWED_THOUGH_GIVEN_A_FUNCTION.containsKey(each.getName())) {
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

    /**
     * Every method that is given a function is a row of the table of what a function is handed and
     * where it goes, or is said not to be followed and why.
     *
     * <p>A function is run by the method it is given to, with what the method chooses, and what it
     * returns goes where the method puts it. That is a fact about the method and nothing else: the
     * second argument of a comparator is the second of two elements, the first of a map's compute is
     * its key, a supplier is handed nothing and what it returns is what the call answers. A method
     * this has no row for is not followed, and is said so where a copy reaches it.
     */
    @Test
    void everyMethodThatIsGivenAFunctionHasARowOrIsSaidNotToBeFollowed() {
        List<String> unread = new ArrayList<>();
        for (Method each : methodsWithFunctions()) {
            if (!HeldCopies.hasACallback(each.getName(), each.getParameterCount())
                    && !NOT_FOLLOWED_THOUGH_GIVEN_A_FUNCTION.containsKey(each.getName())) {
                unread.add(describe(each));
            }
        }

        assertEquals(List.of(), unread.stream().distinct().sorted().toList(),
                "a method is given a function and has no row of what the function is handed and"
                        + " where its result goes, so a copy that reaches it, or that the function"
                        + " makes, is not followed there");
    }

    /** The control: what is said not to be followed is a method that is given a function. */
    @Test
    void whatIsSaidNotToBeFollowedIsGivenAFunction() {
        Set<String> given = new TreeSet<>();
        methodsWithFunctions().forEach(each -> given.add(each.getName()));

        List<String> notGiven = new ArrayList<>();
        for (String name : NOT_FOLLOWED_THOUGH_GIVEN_A_FUNCTION.keySet()) {
            if (!given.contains(name) && !IN_NEWER_JDKS_ONLY.contains(name)) {
                notGiven.add(name);
            }
        }

        assertEquals(List.of(), notGiven.stream().sorted().toList(),
                "a method said not to be followed is not given a function by any class read here");
    }

    /**
     * Every method that is handed an object, or an array of them, to make text of or to ask
     * something of is one the reading has a word for.
     *
     * <p>The text of a container is the text of what it holds, and a call that makes text is known
     * by its name. The library has more of them than anyone lists, so they are put to the table the
     * way the collections are: a method added to these classes fails until it is read.
     */
    @Test
    void everyMethodThatIsHandedAnObjectToMakeTextOfIsOneTheReadingKnows() {
        List<String> unread = new ArrayList<>();
        for (Class<?> host : List.of(String.class, StringBuilder.class, StringBuffer.class,
                Objects.class, PrintStream.class, Formatter.class, MessageFormat.class)) {
            for (Method each : host.getMethods()) {
                boolean handedAnObject = Arrays.stream(each.getParameterTypes()).anyMatch(
                        type -> type == Object.class || type == Object[].class);
                if (handedAnObject && !HeldCopies.understands(each.getName(),
                        each.getParameterCount())) {
                    unread.add(host.getSimpleName() + "." + each.getName() + "/"
                            + each.getParameterCount());
                }
            }
        }

        assertEquals(List.of(), unread.stream().distinct().sorted().toList(),
                "a method is handed an object and is not one the reading knows: if it makes text of"
                        + " it a container that holds a copy says the copy, and if it does not it"
                        + " is listed here");
    }

    /**
     * Every method that is given an array or a container reads it or writes into it, and the ones
     * that write are the ones the reading puts what the receiver holds into.
     *
     * <p>A call has three places an effect lands: what it answers, the object it is made on, and the
     * arrays and containers it is given. The first two are in every row of the tables; the third
     * is the one a row of a table that is read by name is likely to leave out, for a method that
     * answers an array and fills the one it was given looks like a method that only answers one.
     * So each method with such a parameter says which it is, here.
     */
    @Test
    void everyMethodGivenAnArrayOrAContainerReadsItOrWritesIntoIt() {
        List<String> unsaid = new ArrayList<>();
        for (Method each : methodsGivenAnArrayOrAContainer()) {
            String owner = each.getDeclaringClass().getName().replace('.', '/');
            boolean writes = each.getParameterCount() > 0 && (Modifier.isStatic(each.getModifiers())
                    ? HeldCopies.writesIntoItsArgument(owner, each.getName(),
                            each.getParameterCount())
                    : HeldCopies.writesIntoItsArgument(each.getName(), each.getParameterCount()));
            // The wrappers are a family by name, which another test holds to wrapping a container.
            boolean wraps = each.getName().startsWith("unmodifiable")
                    || each.getName().startsWith("synchronized")
                    || each.getName().startsWith("checked");
            if (!writes && !wraps && !READS_WHAT_IT_IS_GIVEN.containsKey(each.getName())) {
                unsaid.add(describe(each));
            }
        }

        assertEquals(List.of(), unsaid.stream().distinct().sorted().toList(),
                "a method is given an array or a container and it is not said whether it reads it or"
                        + " writes into it, so a copy it writes there is not followed");
    }

    /** What a method does with an array or a container it is given that only reads it. */
    private static final Map<String, String> READS_WHAT_IT_IS_GIVEN = readsWhatItIsGiven();

    private static Map<String, String> readsWhatItIsGiven() {
        Map<String, String> out = new TreeMap<>();
        say(out, "reads the container it is given and puts what it holds in the one it is made on",
                "addAll", "addAllAbsent", "putAll");
        say(out, "asks something of what it is given and answers a number or a truth",
                "containsAll", "removeAll", "retainAll", "disjoint", "frequency", "binarySearch",
                "compare", "equals", "mismatch", "deepEquals", "hashCode", "deepHashCode", "hash",
                "indexOfSubList", "lastIndexOfSubList");
        say(out, "makes another container, an array or a walk of what it is given, which holds"
                        + " what that did",
                "asList", "copyOf", "copyOfRange", "of", "ofEntries", "ofLazy", "stream",
                "spliterator", "enumeration", "asLifoQueue", "newSetFromMap",
                "newSequencedSetFromMap");
        say(out, "puts what it is given in another order, in the place it is, so that every path"
                        + " of a copy it holds is the one it was",
                "sort", "parallelSort", "reverse", "shuffle", "rotate", "swap");
        say(out, "takes the greatest or the least of what it is given, which is one element out",
                "max", "min");
        say(out, "makes text of what it is given", "toString", "deepToString", "format",
                "formatted", "join");
        say(out, "folds the elements of an array by a function and writes the results in it, which"
                        + " is not followed and is said where a function that returns a copy is"
                        + " given to it",
                "parallelPrefix", "parallelSetAll");
        say(out, "keeps the container it is given as something the program holds elsewhere, which"
                        + " is not followed",
                "setProperties");
        return out;
    }

    private static void say(Map<String, String> into, String reason, String... names) {
        for (String name : names) {
            into.put(name, reason);
        }
    }

    private static List<Method> methodsGivenAnArrayOrAContainer() {
        List<Class<?>> hosts = new ArrayList<>(COLLECTIONS);
        hosts.addAll(List.of(Stream.class, Collections.class, Arrays.class, Objects.class,
                System.class, String.class, StringBuilder.class, StringBuffer.class));
        List<Method> out = new ArrayList<>();
        for (Class<?> host : hosts) {
            for (Method method : host.getMethods()) {
                for (Class<?> parameter : method.getParameterTypes()) {
                    boolean anArray = parameter.isArray() && !parameter.getComponentType()
                            .isPrimitive();
                    boolean aContainer = Collection.class.isAssignableFrom(parameter)
                            || Map.class.isAssignableFrom(parameter);
                    if (anArray || aContainer) {
                        out.add(method);
                        break;
                    }
                }
            }
        }
        return out;
    }

    /**
     * The families the wrappers of {@code Collections} are named in take the container they wrap
     * first, so that the name is enough to know what they hand back.
     */
    @Test
    void everyWrapperOfCollectionsTakesTheContainerItWrapsFirst() {
        List<String> others = new ArrayList<>();
        for (Method each : Collections.class.getMethods()) {
            String name = each.getName();
            boolean aWrapper = name.startsWith("unmodifiable") || name.startsWith("synchronized")
                    || name.startsWith("checked");
            if (!aWrapper) {
                continue;
            }
            Class<?> first = each.getParameterTypes()[0];
            boolean wrapsAContainer = Collection.class.isAssignableFrom(first)
                    || Map.class.isAssignableFrom(first);
            if (!wrapsAContainer || !HeldCopies.understands(name, each.getParameterCount())) {
                others.add(describe(each));
            }
        }

        assertEquals(List.of(), others.stream().distinct().sorted().toList(),
                "a method of Collections is named like a wrapper and does not wrap a container, so"
                        + " the reading that takes the name for the wrapper reads it wrongly");
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

    /**
     * What walks the elements of a walk, a container or an array, and answers a walk of the same
     * element type, walks the same elements: a stream made a cursor, a cursor made a split cursor,
     * a filtered stream. The type says so — it answers a walk of the type variable that the walk
     * it is made on or given is of — and so what the walk held whole it still holds, as a walk's
     * element, whichever of these it passes through.
     */
    @Test
    void whatAnswersAWalkOfTheElementsOfAWalkItIsMadeOnHoldsTheCopiesTheWalkHeld() {
        List<Class<?>> hosts = List.of(Stream.class, BaseStream.class, Iterator.class,
                Spliterator.class, Enumeration.class, Collections.class, Spliterators.class,
                StreamSupport.class, Arrays.class, Collection.class, Iterable.class, List.class);
        List<String> lost = new ArrayList<>();
        int read = 0;
        for (Class<?> host : hosts) {
            for (Method method : host.getMethods()) {
                if (!keepsTheElementsOfAWalkByItsType(method)) {
                    continue;
                }
                read++;
                if (!holdsTheWalkItWasGiven(method)) {
                    lost.add(describe(method));
                }
            }
        }
        assertEquals(List.of(), lost.stream().distinct().sorted().toList(),
                "a method answers a walk of the elements of a walk it is made on or given, and what"
                        + " that held whole is not held by the answer");
        assertTrue(read > 15, "too few methods were read: " + read);
    }

    /**
     * Whether the answer of a call of the method holds, as a walk's element, the copy that what the
     * call was made on and given held whole in a walk, a container and an array.
     */
    private static boolean holdsTheWalkItWasGiven(Method method) {
        String origin = "probe";
        boolean isStatic = Modifier.isStatic(method.getModifiers());
        List<SaltedOrder.Val> args = new ArrayList<>();
        for (Class<?> each : method.getParameterTypes()) {
            String path = isAWalk(each) ? "w" : each.isArray() ? "a"
                    : Iterable.class.isAssignableFrom(each) ? "e" : null;
            args.add(path == null ? SaltedOrder.Val.CLEAN
                    : SaltedOrder.Val.of(SaltedOrder.Tag.held(origin, path)));
        }
        SaltedOrder.Val receiver = isStatic ? SaltedOrder.Val.CLEAN
                : SaltedOrder.Val.of(SaltedOrder.Tag.held(origin,
                        isAWalk(method.getDeclaringClass()) ? "w" : "e"));
        SaltedOrderVocabulary.Call call = new SaltedOrderVocabulary.Call(
                method.getDeclaringClass().getName().replace('.', '/'), method.getName(),
                MethodType.methodType(method.getReturnType(), method.getParameterTypes())
                        .descriptorString(),
                receiver, args, isStatic, true, true, false);
        for (SaltedOrder.Tag each : SaltedOrderVocabulary.of(call).result().tags()) {
            if (each.isHeld() && each.origin().equals(origin) && each.site().startsWith("w")) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether the method answers a walk of the type variable that the walk, container or array it
     * is made on or given is of.
     */
    private static boolean keepsTheElementsOfAWalkByItsType(Method method) {
        Type returned = method.getGenericReturnType();
        if (!(returned instanceof ParameterizedType answer)
                || !isAWalk((Class<?>) answer.getRawType())
                || answer.getActualTypeArguments().length == 0) {
            return false;
        }
        TypeVariable<?> variable = variableOf(answer.getActualTypeArguments()[0]);
        if (variable == null) {
            return false;
        }
        if (!Modifier.isStatic(method.getModifiers())) {
            Class<?> on = method.getDeclaringClass();
            return (isAWalk(on) || Iterable.class.isAssignableFrom(on))
                    && Arrays.asList(on.getTypeParameters()).contains(variable)
                    && on.getTypeParameters()[0].equals(variable);
        }
        for (Type each : method.getGenericParameterTypes()) {
            if (each instanceof ParameterizedType given
                    && (isAWalk((Class<?>) given.getRawType())
                            || Iterable.class.isAssignableFrom((Class<?>) given.getRawType()))
                    && variableOf(given.getActualTypeArguments()[0]) != null
                    && variableOf(given.getActualTypeArguments()[0]).equals(variable)) {
                return true;
            }
            if (each instanceof GenericArrayType array
                    && variable.equals(variableOf(array.getGenericComponentType()))) {
                return true;
            }
        }
        return false;
    }

    private static boolean isAWalk(Class<?> type) {
        return BaseStream.class.isAssignableFrom(type) || Iterator.class.isAssignableFrom(type)
                || Spliterator.class.isAssignableFrom(type)
                || Enumeration.class.isAssignableFrom(type);
    }

    private static TypeVariable<?> variableOf(Type type) {
        if (type instanceof TypeVariable<?> variable) {
            return variable;
        }
        if (type instanceof WildcardType wildcard && wildcard.getUpperBounds().length == 1
                && wildcard.getUpperBounds()[0] instanceof TypeVariable<?> variable) {
            return variable;
        }
        return null;
    }

    /**
     * A writer, a stream or a formatter made over a place to write says what it is told there, and
     * one that keeps what it is told itself does not: every constructor of the library's is read as
     * the one or the other.
     */
    @Test
    void everyConstructorOfAWriterIsOverAPlaceExceptThoseOfTheOnesThatKeepTheirOwnText() {
        List<Class<?>> writers = List.of(Formatter.class, PrintWriter.class, PrintStream.class,
                BufferedWriter.class, OutputStreamWriter.class, FileWriter.class,
                FileOutputStream.class, BufferedOutputStream.class, DataOutputStream.class,
                ObjectOutputStream.class, GZIPOutputStream.class, StringWriter.class,
                CharArrayWriter.class, ByteArrayOutputStream.class);
        List<String> wrong = new ArrayList<>();
        int over = 0;
        for (Class<?> each : writers) {
            for (Constructor<?> made : each.getConstructors()) {
                boolean keepsItsOwn = each == StringWriter.class || each == CharArrayWriter.class
                        || each == ByteArrayOutputStream.class
                        || (each == Formatter.class && Arrays.stream(made.getParameterTypes())
                                .allMatch(type -> type == Locale.class));
                String descriptor = MethodType.methodType(void.class, made.getParameterTypes())
                        .descriptorString();
                boolean read = HeldCopies.writesWhereItWasMadeOver(
                        each.getName().replace('.', '/'), descriptor);
                over += read ? 1 : 0;
                if (read == keepsItsOwn) {
                    wrong.add(each.getSimpleName() + Arrays.toString(made.getParameterTypes())
                            + " is read as " + (read ? "over a place" : "keeping its own text"));
                }
            }
        }
        assertEquals(List.of(), wrong, "a constructor was read as the wrong kind");
        assertTrue(over > 0, "no constructor over a place was read");
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

    /** Every method, static or not, of these and of the streams, that has a function parameter. */
    private static List<Method> methodsWithFunctions() {
        List<Class<?>> hosts = new ArrayList<>(COLLECTIONS);
        hosts.addAll(List.of(Stream.class, Collections.class, Arrays.class, Objects.class));
        List<Method> out = new ArrayList<>();
        for (Class<?> each : hosts) {
            for (Method method : each.getMethods()) {
                for (Class<?> parameter : method.getParameterTypes()) {
                    if (parameter.isAnnotationPresent(FunctionalInterface.class)) {
                        out.add(method);
                        break;
                    }
                }
            }
        }
        return out;
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
