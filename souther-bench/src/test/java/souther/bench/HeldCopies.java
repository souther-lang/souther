package souther.bench;

import souther.bench.SaltedOrder.Kind;
import souther.bench.SaltedOrder.Tag;
import souther.bench.SaltedOrder.Val;
import souther.bench.SaltedOrderVocabulary.Call;
import souther.bench.SaltedOrderVocabulary.Feed;
import souther.bench.SaltedOrderVocabulary.Outcome;
import souther.bench.SaltedOrderVocabulary.Push;

import java.io.OutputStream;
import java.io.Writer;
import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.Formatter;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.BaseStream;

/**
 * What a call does to the copies a container holds whole.
 *
 * <p>A copy put into a list, or beside a key of a map, leaves the order of the container where it
 * was: the container's order is the order things were put in, and holds nothing of how the copy
 * iterates. What changes is what can be taken out of it, so the container carries, for each copy,
 * a {@link Kind#HELD} tag whose site is the path of slots down to it, outermost first. A slot says
 * what the thing is that holds the next: {@code e} the element or the value of a container,
 * {@code a} the element of an array, {@code w} the element of a stream or a cursor, {@code k} a
 * key. A list of lists of copies says {@code ee}, a map from a copy to anything says {@code k},
 * and an array of lists of copies says {@code ae}.
 *
 * <p><b>What kind of thing holds a copy is in the path, and so travels with it.</b> A mark on the
 * value is lost where the value is handed to a method, kept in a field or answered by a call; the
 * tag is not. What a text of a value says, and what the elements of a stream are, are read off the
 * path. A view that writes through to another container is a {@link Kind#VIEW} tag for the same
 * reason.
 *
 * <p><b>A path is at most {@link #MAX_DEPTH} slots.</b> Code that wraps a value as often as a
 * number says has no deepest container, and a path that grew with it would give the reading no
 * fixed point. A path that would be longer is widened to its first slots and {@code *}, which says
 * that the copy is that deep or deeper: taking a slot out of it may be the copy itself, or may be a
 * container that still holds it, and both are said. The set of paths is finite, so the reading
 * settles, and a wider path says more than a narrower one.
 *
 * <p>A path is all a container carries, so nothing is made per element or per call. What takes
 * something out says which slot, and the tag becomes the copy itself where the path is spent and
 * stays a held one where it is not. That is one table, here, and it is joined to what the order
 * reading says of the same call and does not stand in for it: a container can hold a copy and be
 * made of another's elements at once, and each is read.
 *
 * <p><b>An operation is a name and the number of arguments it is given.</b> Where the value an
 * operation stores stands among its arguments is a property of that pair and of nothing else:
 * {@code replace} of a key and a value stores its second argument and {@code replace} of a key, the
 * value it expects and a value stores its third. {@link #placementOf} is that table, and a test
 * puts every method of the collections of the library that is named like one that stores to it.
 * What kind of container a call is made on is read off the type it is declared on, by the type
 * hierarchy, and not off the spelling of its name.
 *
 * <p><b>A container that holds a copy is never handed to something unread in silence.</b> What a
 * call does with one is a word of this table (it stores, takes out, makes a view or a copy, clears,
 * asks only what is held, runs a function over it, makes text) or it is said so as a finding that
 * names the copy. A view, a cursor or an entry of another container writes through to it, which is
 * not followed: what is stored in one is said so as well, since it is stored in the container it
 * is of.
 *
 * <p><b>What this does not follow.</b> A container is a set of paths and not of keys, so a put to
 * a key a copy was put to before does not take the copy out: that is read as holding both, which
 * says more than the code does. {@code clear} is the only operation that takes something out. A
 * copy that is only held and never read by anything that takes it out ends nowhere, and the test
 * that asks where every copy ends is what says so.
 *
 * <p><b>What a function is handed, and where its result goes, is a row.</b> A method that runs a
 * function says which of its arguments is the function, which container the function is run over,
 * what each of its parameters is (an element, a key, one of the call's own arguments) and where
 * what it returns goes ({@link Into}). The row does not depend on a container holding anything
 * when the call is made: a function that makes a copy and is handed to a {@code map} returns it to
 * the call whatever the stream was. A method with no row is not followed, and that is said where
 * a container that holds a copy is handed to it and where a function that returns a copy is.
 * The bulk operations of a concurrent map and the comparisons of arrays by a comparator are
 * those, and a test puts every method of the library that is given a function to the table.
 *
 * <p><b>The text of a value is read off its path.</b> A container says what it holds, element by
 * element; an array and a stream or a cursor say what they are. Only a call that makes text of the
 * elements of an array (the text of an array, the arguments of a format) says what an array holds,
 * and only the deep text goes into an array inside it.
 */
final class HeldCopies {

    /** The most slots a path names before it is widened. */
    static final int MAX_DEPTH = 3;

    private static final String ANY = "*";

    /** The element or the value of a container. */
    private static final String ELEMENT = "e";

    /** The element of an array. */
    private static final String ARRAY_ELEMENT = "a";

    /** The element of a stream or a cursor. */
    private static final String WALK_ELEMENT = "w";

    /** Every slot that holds an element, of whatever it is an element of. */
    private static final String ELEMENTS = "eaw";

    private static final String KEY = "k";

    /**
     * Where what a function returns goes, in the call that was given the function: nowhere, as a
     * predicate's answer does; an element of the stream the call hands back, as the function of a
     * {@code map} makes one; an element of the optional it hands back; what the container the
     * function returned held, as a {@code flatMap} spreads it; what the call hands back as it is,
     * as a supplier's does; an element of the container, or of the array, the call is made on, as a
     * {@code replaceAll} or a {@code setAll} puts it; or the container's element and what the call
     * hands back, as a {@code compute} puts the value in the map and answers it.
     */
    enum Into {
        NOTHING,
        AS_WALK_ELEMENTS,
        AS_ELEMENTS,
        AS_THEY_ARE,
        AS_RETURNED,
        KEPT_AS_ELEMENTS,
        KEPT_AS_ARRAY_ELEMENTS,
        KEPT_AND_RETURNED
    }

    /** What a function a call is given is handed, one source for each of its parameters. */
    private enum Source {
        /** An element of the container, or the value of an entry. */
        ELEMENT,
        /** A key of the container. */
        KEY,
        /** The first argument of the call, which is not the function. */
        FIRST_ARGUMENT,
        /** The second argument of the call. */
        SECOND_ARGUMENT
    }

    /** Which kinds of thing a row is about, by the type the call is declared on. */
    private enum On {
        ANY,
        MAPS,
        NOT_MAPS,
        OPTIONALS,
        STREAMS,
        OTHER
    }

    /**
     * What the call of this name with this many arguments does with a function it is given.
     *
     * @param function  which argument is the function
     * @param container which argument is the container the function is run over: -1 is the one the
     *                  call is made on
     * @param on        the kind of thing the row is about
     * @param handed    what each parameter of the function is
     * @param into      where what the function returns goes
     */
    private record Callback(String name, int arity, int function, int container, On on,
                            List<Source> handed, Into into) {}

    private static final List<Callback> CALLBACKS = callbacks();

    /** Where, among a call's arguments, the key and the value it stores are; none is -1. */
    record Placement(int key, int value) {

        static final int NONE = -1;
    }

    private static final Map<String, Map<Integer, Placement>> PLACEMENTS = placements();

    private static final Set<String> PUTS_ALL = Set.of("addAll", "putAll", "addAllAbsent");

    /** What takes the one value out that a container holds, or hands the one it held back. */
    private static final Set<String> TAKES_THE_ONLY_ONE_OUT = Set.of(
            "get", "getOrDefault", "remove", "orElse", "orElseGet", "orElseThrow", "getValue",
            "firstElement", "lastElement", "take", "takeFirst", "takeLast", "put", "putIfAbsent",
            "replace", "set", "merge", "compute", "computeIfAbsent", "computeIfPresent",
            "putFirst", "putLast", "push", "setValue");

    /** What takes a key out of a map, and what takes an entry, which holds a key and a value. */
    private static final Set<String> TAKES_A_KEY_OUT = Set.of(
            "getKey", "firstKey", "lastKey", "lowerKey", "higherKey", "floorKey", "ceilingKey");

    private static final Set<String> TAKES_AN_ENTRY_OUT = Set.of(
            "firstEntry", "lastEntry", "pollFirstEntry", "pollLastEntry", "lowerEntry",
            "higherEntry", "floorEntry", "ceilingEntry");

    /**
     * What asks a container something that cannot reveal a copy it holds or keep one: how many it
     * holds, whether it holds one, where one stands, a hash of them all. A hash is the same
     * whichever order the elements are met in, which is the contract of the sets that are copies.
     */
    private static final Set<String> ASKS_ONLY = Set.of(
            "size", "isEmpty", "contains", "containsAll", "containsKey", "containsValue", "equals",
            "hashCode", "indexOf", "lastIndexOf", "isPresent", "hasNext", "hasPrevious",
            "hasMoreElements", "nextIndex", "previousIndex", "removeAll", "retainAll",
            "removeFirstOccurrence", "removeLastOccurrence", "removeElement",
            "removeAllElements", "removeElementAt", "removeRange", "trimToSize", "ensureCapacity",
            "capacity", "setSize", "comparator", "isNull", "nonNull", "identityHashCode", "hash",
            "frequency", "disjoint", "binarySearch", "checkIndex", "swap", "rotate", "reverse",
            "shuffle", "sort", "elementCount", "remainingCapacity", "empty", "mappingCount",
            "deepEquals", "toIdentityString", "contentEquals", "compare", "compareTo");

    /** What makes text of what it is handed, so that a container says the copies it holds. */
    private static final Set<String> MAKES_TEXT_OF_ITS_ARGUMENTS = Set.of(
            "valueOf", "format", "formatted", "printf", "append", "insert", "print", "println",
            "toString", "deepToString", "formatToCharacterIterator");

    /** What hands back the container it is given, or one that holds what it did. */
    private static final Set<String> HANDS_BACK_THE_CONTAINER = Set.of(
            "requireNonNull", "requireNonNullElse", "requireNonNullElseGet", "concat");

    /** What stores what it holds in a container it is given. */
    private static final Set<String> STORES_WHAT_IT_HOLDS_IN_ITS_ARGUMENT = Set.of(
            "drainTo", "copyInto");

    private static final Set<String> KEY_VIEWS = Set.of(
            "keySet", "sequencedKeySet", "navigableKeySet", "descendingKeySet");

    private static final Set<String> VALUE_VIEWS = Set.of("values", "sequencedValues");

    private static final Set<String> ENTRY_VIEWS = Set.of("entrySet", "sequencedEntrySet");

    /** What walks the keys, or the values, of a map as an enumeration. */
    private static final Set<String> WALKS_THE_KEYS = Set.of("keys");

    private static final Set<String> WALKS_THE_VALUES = Set.of("elements");

    private static final Set<String> HOLDS_ITS_ARGUMENTS = Set.of(
            "of", "asList", "singleton", "singletonList", "ofNullable");

    private static final Set<String> HANDS_BACK_ITS_ARGUMENT = Set.of(
            "copyOf", "copyOfRange", "stream");

    private static final Set<String> WRAPS_ITS_ARGUMENT_FAMILIES_BY_NAME = Set.of(
            "unmodifiable", "synchronized", "checked");

    private static final Set<String> SAME_ELEMENTS_IN_ANOTHER_FORM = Set.of(
            "toList", "toArray", "sorted", "clone", "asIterator", "trySplit");

    /** What the library's own types are, by name, to be read off their hierarchy. */
    private static final Map<String, Optional<Class<?>>> TYPES = new ConcurrentHashMap<>();

    private HeldCopies() {}

    // ---- what a type is

    /** Whether the type a call is declared on is, or extends, this one, by its hierarchy. */
    static boolean isA(String internalName, Class<?> type) {
        Optional<Class<?>> found = TYPES.computeIfAbsent(internalName, name -> {
            try {
                return Optional.of(Class.forName(name.replace('/', '.'), false,
                        HeldCopies.class.getClassLoader()));
            } catch (ClassNotFoundException | LinkageError unreadable) {
                return Optional.empty();
            }
        });
        return found.isPresent() && type.isAssignableFrom(found.get());
    }

    /** Whether the type is a map of any kind: {@code Hashtable} and {@code Properties} are. */
    static boolean isAMap(String internalName) {
        return isA(internalName, Map.class);
    }

    private static boolean isAnEntry(String internalName) {
        return isA(internalName, Map.Entry.class);
    }

    private static On kindOf(String internalName) {
        if (isAMap(internalName)) {
            return On.MAPS;
        }
        if (internalName.equals("java/util/Optional")) {
            return On.OPTIONALS;
        }
        return internalName.startsWith("java/util/stream/") ? On.STREAMS : On.OTHER;
    }

    // ---- the tables

    private static Map<String, Map<Integer, Placement>> placements() {
        Map<String, Map<Integer, Placement>> out = new HashMap<>();
        for (String name : List.of("add", "addFirst", "addLast", "push", "addElement",
                "addIfAbsent", "offer", "offerFirst", "offerLast", "set", "setValue", "put",
                "putFirst", "putLast")) {
            row(out, name, 1, Placement.NONE, 0);
        }
        for (String name : List.of("add", "set")) {
            row(out, name, 2, Placement.NONE, 1);
        }
        for (String name : List.of("offer", "offerFirst", "offerLast")) {
            row(out, name, 3, Placement.NONE, 0);
        }
        row(out, "setElementAt", 2, Placement.NONE, 0);
        row(out, "insertElementAt", 2, Placement.NONE, 0);
        for (String name : List.of("put", "putFirst", "putLast", "putIfAbsent", "replace")) {
            row(out, name, 2, 0, 1);
        }
        row(out, "replace", 3, 0, 2);
        row(out, "merge", 3, 0, 1);
        return out;
    }

    private static void row(Map<String, Map<Integer, Placement>> into, String name, int arity,
                            int key, int value) {
        into.computeIfAbsent(name, each -> new HashMap<>()).put(arity, new Placement(key, value));
    }

    /**
     * The functions the library's collections and streams run, and what each is handed and does.
     * A function handed to anything that is not here is not followed: it is said so where a
     * container that holds a copy is handed to it, and where what the function returns is one.
     */
    private static List<Callback> callbacks() {
        List<Callback> out = new ArrayList<>();
        List<Source> element = List.of(Source.ELEMENT);
        List<Source> two = List.of(Source.ELEMENT, Source.ELEMENT);
        List<Source> keyAndValue = List.of(Source.KEY, Source.ELEMENT);
        out.add(new Callback("forEach", 1, 0, -1, On.NOT_MAPS, element, Into.NOTHING));
        out.add(new Callback("forEach", 1, 0, -1, On.MAPS, keyAndValue, Into.NOTHING));
        for (String name : List.of("forEachRemaining", "tryAdvance", "forEachOrdered", "removeIf",
                "ifPresent",
                "filter", "peek", "takeWhile", "dropWhile", "anyMatch", "allMatch", "noneMatch")) {
            out.add(new Callback(name, 1, 0, -1, On.ANY, element, Into.NOTHING));
        }
        out.add(new Callback("ifPresentOrElse", 2, 0, -1, On.ANY, element, Into.NOTHING));
        out.add(new Callback("replaceAll", 1, 0, -1, On.NOT_MAPS, element,
                Into.KEPT_AS_ELEMENTS));
        out.add(new Callback("replaceAll", 1, 0, -1, On.MAPS, keyAndValue,
                Into.KEPT_AS_ELEMENTS));
        for (String name : List.of("sort", "sorted", "min", "max")) {
            out.add(new Callback(name, 1, 0, -1, On.ANY, two, Into.NOTHING));
        }
        out.add(new Callback("reduce", 1, 0, -1, On.ANY, two, Into.AS_ELEMENTS));
        out.add(new Callback("reduce", 2, 1, -1, On.ANY, two, Into.AS_RETURNED));
        for (String name : List.of("map", "mapToObj")) {
            out.add(new Callback(name, 1, 0, -1, On.STREAMS, element, Into.AS_WALK_ELEMENTS));
        }
        out.add(new Callback("map", 1, 0, -1, On.OPTIONALS, element, Into.AS_ELEMENTS));
        out.add(new Callback("flatMap", 1, 0, -1, On.ANY, element, Into.AS_THEY_ARE));
        for (String name : List.of("compute", "computeIfPresent")) {
            out.add(new Callback(name, 2, 1, -1, On.ANY,
                    List.of(Source.FIRST_ARGUMENT, Source.ELEMENT), Into.KEPT_AND_RETURNED));
        }
        out.add(new Callback("computeIfAbsent", 2, 1, -1, On.ANY,
                List.of(Source.FIRST_ARGUMENT), Into.KEPT_AND_RETURNED));
        out.add(new Callback("merge", 3, 2, -1, On.ANY,
                List.of(Source.ELEMENT, Source.SECOND_ARGUMENT), Into.KEPT_AND_RETURNED));
        out.add(new Callback("orElseGet", 1, 0, -1, On.ANY, List.of(), Into.AS_RETURNED));
        out.add(new Callback("or", 1, 0, -1, On.ANY, List.of(), Into.AS_THEY_ARE));
        out.add(new Callback("requireNonNullElseGet", 2, 1, -1, On.ANY, List.of(),
                Into.AS_RETURNED));
        out.add(new Callback("generate", 1, 0, -1, On.STREAMS, List.of(), Into.AS_WALK_ELEMENTS));
        for (String name : List.of("sort", "max", "min")) {
            out.add(new Callback(name, 2, 1, 0, On.ANY, two, Into.NOTHING));
        }
        out.add(new Callback("sort", 4, 3, 0, On.ANY, two, Into.NOTHING));
        out.add(new Callback("setAll", 2, 1, 0, On.ANY, List.of(), Into.KEPT_AS_ARRAY_ELEMENTS));
        return out;
    }

    /** The row for this call, if the library's function it is given has one. */
    private static Optional<Callback> callbackOf(Call call) {
        On declaredOn = kindOf(call.owner());
        for (Callback each : CALLBACKS) {
            boolean kind = each.on() == On.ANY || each.on() == declaredOn
                    || (each.on() == On.NOT_MAPS && declaredOn != On.MAPS);
            if (each.name().equals(call.name()) && each.arity() == call.args().size() && kind) {
                return Optional.of(each);
            }
        }
        return Optional.empty();
    }

    /** Whether any call of this name with this many arguments is one the table has a row for. */
    static boolean hasACallback(String name, int arity) {
        for (Callback each : CALLBACKS) {
            if (each.name().equals(name) && each.arity() == arity) {
                return true;
            }
        }
        return false;
    }

    /** Where the call of this name with this many arguments stores what it stores, if it does. */
    static Optional<Placement> placementOf(String name, int arity) {
        return Optional.ofNullable(PLACEMENTS.getOrDefault(name, Map.of()).get(arity));
    }

    /** Whether the call puts every element of the container it is given in the one it is made on. */
    static boolean putsAllIn(String name) {
        return PUTS_ALL.contains(name);
    }

    /** Whether the call of this name hands back a value, a key or an element a container held. */
    static boolean takesOut(String name) {
        return TAKES_A_KEY_OUT.contains(name) || TAKES_AN_ENTRY_OUT.contains(name)
                || SaltedOrderVocabulary.takesOneOut(name)
                || TAKES_THE_ONLY_ONE_OUT.contains(name);
    }

    // ---- a call

    /** What the call does to held copies, joined to what the order reading made of it. */
    static Outcome through(Call call, Outcome order) {
        Outcome out = madeAWindow(call, withText(call, order));
        List<Push> intoArguments = putIntoArguments(call);
        if (!intoArguments.isEmpty()) {
            out = SaltedOrderVocabulary.alsoPushing(out, intoArguments);
        }
        if (!SaltedOrderVocabulary.inTheCollectionsLibrary(call.owner())) {
            return out;
        }
        Set<Tag> handedBack = handedBack(call);
        if (!handedBack.isEmpty()) {
            out = out.holding(handedBack);
        }
        Set<Tag> put = put(call);
        if (!put.isEmpty()) {
            out = SaltedOrderVocabulary.alsoPushing(out, List.of(new Push(call.receiver(), put)));
        }
        if (call.name().equals("clear") && !call.isStatic() && !held(call.receiver()).isEmpty()) {
            out = SaltedOrderVocabulary.alsoClearing(out, call.receiver());
        }
        Feed handedToTheFunctions = handedToFunctions(call);
        if (handedToTheFunctions != null) {
            out = out.feeding(List.of(handedToTheFunctions), false);
        }
        return markedAsAView(call, out);
    }

    /**
     * What a call answers that writes through to the container it was made on is marked by a tag,
     * so that a put to it is known not to reach any object that is tracked, wherever the object
     * goes. The entries of a map are views of it, and so is the cursor of a list, a key set, a
     * sublist; what is taken out of the entries of a map is an entry.
     */
    private static Outcome markedAsAView(Call call, Outcome out) {
        if (call.isStatic() || !call.returnsAReference()) {
            return out;
        }
        String name = call.name();
        Tag mark;
        if (isEntriesOfAMap(call.receiver())) {
            if (takesOut(name) && !TAKES_A_KEY_OUT.contains(name)) {
                mark = Tag.view();
            } else if (SaltedOrderVocabulary.keepsTheElementsOfAWalk(name)
                    || SaltedOrderVocabulary.startsATraversal(name)
                    || SaltedOrderVocabulary.isAView(name)) {
                mark = Tag.entriesOfAMap();
            } else {
                return out;
            }
        } else if (ENTRY_VIEWS.contains(name)) {
            mark = Tag.entriesOfAMap();
        } else if (KEY_VIEWS.contains(name) || VALUE_VIEWS.contains(name)
                || WALKS_THE_KEYS.contains(name) || WALKS_THE_VALUES.contains(name)
                || SaltedOrderVocabulary.isAView(name) || name.equals("listIterator")) {
            mark = Tag.view();
        } else {
            return out;
        }
        return out.holding(Set.of(mark));
    }

    private static boolean isEntriesOfAMap(Val value) {
        for (Tag each : value.tags()) {
            if (each.isEntriesOfAMap()) {
                return true;
            }
        }
        return false;
    }

    private static boolean isAView(Val value) {
        for (Tag each : value.tags()) {
            if (each.isAView()) {
                return true;
            }
        }
        return false;
    }

    // ---- text

    /** The text a call makes of the containers it is handed says the copies they hold, in order. */
    private static Outcome withText(Call call, Outcome order) {
        Set<Tag> said = textOfHeld(call);
        if (said.isEmpty()) {
            return order;
        }
        Outcome out = order;
        // What is said into something that keeps what it is told is kept by it: the text is asked
        // of it later, by a call that has no copy in sight.
        boolean intoSomethingThatKeepsIt = !call.isStatic() && accumulatesText(call.owner());
        if (intoSomethingThatKeepsIt) {
            out = SaltedOrderVocabulary.alsoPushing(out, List.of(new Push(call.receiver(), said)));
        }
        return call.returnsAReference() ? out.holding(said) : out;
    }

    /**
     * A writer, a stream or a formatter made over where it writes is a window onto that place: what
     * is said into it is said there, and read from there by whatever holds the place. The window
     * is marked by a tag so that this is known wherever it goes.
     */
    private static Outcome madeAWindow(Call call, Outcome out) {
        if (call.isStatic() || !call.name().equals("<init>")
                || !writesWhereItWasMadeOver(call.owner(), call.descriptor())) {
            return out;
        }
        return SaltedOrderVocabulary.alsoPushing(out,
                List.of(new Push(call.receiver(), Set.of(Tag.window()))));
    }

    /**
     * Whether a constructor of this class makes it over a place to write to. A class that keeps
     * what it is told itself is made over none: its constructors take a size, a locale or a
     * charset and nothing to write into.
     */
    static boolean writesWhereItWasMadeOver(String owner, String descriptor) {
        if (!isASink(owner)) {
            return false;
        }
        for (ClassDesc each : MethodTypeDesc.ofDescriptor(descriptor).parameterList()) {
            String type = each.descriptorString();
            if (!type.startsWith("L")) {
                continue;
            }
            String named = type.substring(1, type.length() - 1);
            if (WRITTEN_TO_BY_NAME.contains(named) || isA(named, Appendable.class)
                    || isA(named, OutputStream.class)) {
                return true;
            }
        }
        return false;
    }

    /** What a class that writes to a place is given to name it, other than another to write to. */
    private static final Set<String> WRITTEN_TO_BY_NAME = Set.of(
            "java/lang/String", "java/io/File", "java/nio/file/Path", "java/io/FileDescriptor");

    /** Whether the type says what it is told into a place, which it may have been made over. */
    private static boolean isASink(String internalName) {
        return isA(internalName, Formatter.class) || isA(internalName, Writer.class)
                || isA(internalName, OutputStream.class);
    }

    /**
     * Whether the call is made on a window: one marked as such, or one that something handed in
     * and nothing here made, which is a window onto wherever its holder made it.
     */
    private static boolean onAWindow(Call call) {
        if (call.isStatic() || call.name().equals("<init>")) {
            return false;
        }
        Val receiver = call.receiver();
        for (Tag each : receiver.tags()) {
            if (each.isAWindow()) {
                return true;
            }
        }
        return receiver.alloc() < 0 && receiver.home() != null && isASink(call.owner());
    }

    /** Whether what is of this type keeps the text it is told, to say it when it is asked. */
    private static boolean accumulatesText(String internalName) {
        return isA(internalName, StringBuilder.class) || isA(internalName, StringBuffer.class)
                || isA(internalName, Formatter.class);
    }

    /**
     * The order each copy held in what the call is handed is said in, where the call makes text of
     * it. The text of a container is the text of what it holds, and a set that is a copy says its
     * elements in the order it iterates; an array and a stream say what they are.
     */
    static Set<Tag> textOfHeld(Call call) {
        String name = call.name();
        boolean ofTheReceiver = name.equals("toString") && !call.isStatic()
                && call.args().isEmpty();
        if (!ofTheReceiver && !MAKES_TEXT_OF_ITS_ARGUMENTS.contains(name)) {
            return Set.of();
        }
        boolean ofArrays = call.isStatic() && call.owner().equals("java/util/Arrays");
        boolean deep = ofArrays && name.equals("deepToString");
        List<ClassDesc> parameters = MethodTypeDesc.ofDescriptor(call.descriptor())
                .parameterList();
        Set<Tag> out = new LinkedHashSet<>();
        for (int at = 0; at < call.args().size(); at++) {
            // The elements of an array are what these say: the text of an array, and the
            // arguments of a format, which are handed over as one.
            boolean saysItsElements = (ofArrays && (name.equals("toString") || deep))
                    || (at < parameters.size()
                            && parameters.get(at).descriptorString().equals("[Ljava/lang/Object;"));
            addTextOf(call.args().get(at), out, saysItsElements, deep);
        }
        if (ofTheReceiver) {
            addTextOf(call.receiver(), out, false, false);
        }
        return out;
    }

    private static void addTextOf(Val value, Set<Tag> into, boolean saysItsElements,
                                  boolean deep) {
        for (Tag each : value.tags()) {
            if (!each.isHeld()) {
                continue;
            }
            String path = each.site();
            if (saysItsElements && path.startsWith(ARRAY_ELEMENT)) {
                path = path.substring(ARRAY_ELEMENT.length());
            }
            if (textReaches(path, deep)) {
                into.add(new Tag(Kind.SEQUENCE, each.origin()));
            }
        }
    }

    /**
     * Whether the text of what holds a copy at this path goes as far as the copy. A container says
     * each element, and the element says what it holds; an array and a stream or a cursor say
     * what they are, and say what they hold only where the text is the deep text of an array.
     * Where the path goes on past what is known, it may.
     */
    static boolean textReaches(String path, boolean deepThroughArrays) {
        for (int at = 0; at < path.length(); at++) {
            String slot = path.substring(at, at + 1);
            if (slot.equals(ANY)) {
                return true;
            }
            if (slot.equals(WALK_ELEMENT) || (slot.equals(ARRAY_ELEMENT) && !deepThroughArrays)) {
                return false;
            }
        }
        return true;
    }

    // ---- stores into arguments

    /** What the call puts in the containers it is given, which are not the one it is made on. */
    private static List<Push> putIntoArguments(Call call) {
        String name = call.name();
        List<Val> args = call.args();
        String owner = call.owner();
        if (!call.isStatic()) {
            if (!writesIntoItsArgument(name, args.size()) || args.isEmpty()) {
                return List.of();
            }
            // A container drains into one, and is copied into an array: a vector, or a collection
            // asked for its elements in an array it is given, which it fills where it has room.
            Set<Tag> held = held(call.receiver());
            return pushed(args.get(0), name.equals("drainTo") ? held
                    : retargeted(held, "ew", ARRAY_ELEMENT));
        }
        if (!writesIntoItsArgument(owner, name, args.size())) {
            return List.of();
        }
        if (owner.equals("java/lang/System") && name.equals("arraycopy") && args.size() == 5) {
            return pushed(args.get(2), held(args.get(0)));
        }
        if (owner.equals("java/util/Collections")) {
            if (name.equals("addAll") && args.size() == 2) {
                return pushed(args.get(0), retargeted(held(args.get(1)), "aw", ELEMENT));
            }
            if (name.equals("copy") && args.size() == 2) {
                return pushed(args.get(0), held(args.get(1)));
            }
            if (name.equals("fill") && args.size() == 2) {
                return pushed(args.get(0), putIn(ELEMENT, args.get(1)));
            }
            if (name.equals("replaceAll") && args.size() == 3) {
                return pushed(args.get(0), putIn(ELEMENT, args.get(2)));
            }
        }
        if (owner.equals("java/util/Arrays") && name.equals("fill") && !args.isEmpty()) {
            return pushed(args.get(0), putIn(ARRAY_ELEMENT, args.get(args.size() - 1)));
        }
        return List.of();
    }

    private static List<Push> pushed(Val into, Set<Tag> tags) {
        return tags.isEmpty() ? List.of() : List.of(new Push(into, tags));
    }

    // ---- what is read

    /**
     * Whether the operation of this name is one this reads, for a container that holds a copy: it
     * stores, takes out, makes a view or a copy, clears, asks only what is held, or makes text.
     * What is none of those is not followed, and is said so when a container that holds a copy is
     * handed to it.
     */
    static boolean understands(String name, int arity) {
        return placementOf(name, arity).isPresent() || PUTS_ALL.contains(name)
                || takesOut(name) || KEY_VIEWS.contains(name) || VALUE_VIEWS.contains(name)
                || ENTRY_VIEWS.contains(name) || WALKS_THE_KEYS.contains(name)
                || WALKS_THE_VALUES.contains(name) || SaltedOrderVocabulary.isAView(name)
                || SaltedOrderVocabulary.keepsTheElementsOfAWalk(name)
                || SaltedOrderVocabulary.startsATraversal(name)
                || SAME_ELEMENTS_IN_ANOTHER_FORM.contains(name) || name.equals("clear")
                || name.equals("<init>") || ASKS_ONLY.contains(name)
                || hasACallback(name, arity)
                || STORES_WHAT_IT_HOLDS_IN_ITS_ARGUMENT.contains(name)
                || (name.equals("search") && arity <= 2)
                || MAKES_TEXT_OF_ITS_ARGUMENTS.contains(name)
                || HOLDS_ITS_ARGUMENTS.contains(name) || HANDS_BACK_ITS_ARGUMENT.contains(name)
                || HANDS_BACK_THE_CONTAINER.contains(name) || wrapsItsArgument(name)
                || name.equals("entry") || name.equals("singletonMap") || name.equals("nCopies")
                || name.equals("ofEntries") || name.equals("arraycopy")
                || name.equals("fill") || name.equals("copy") || name.equals("replaceAll");
    }

    /** Whether the name is one of the families that wrap the container they are given. */
    private static boolean wrapsItsArgument(String name) {
        for (String family : WRAPS_ITS_ARGUMENT_FAMILIES_BY_NAME) {
            if (name.startsWith(family)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The copies a call is handed, held whole, that it is not known what it does with, and the
     * copies it stores in something that is a view of another container or came from one, which
     * the storing does not reach.
     */
    static Set<String> unresolvedBy(Call call) {
        Set<String> out = new LinkedHashSet<>();
        boolean givenAFunction = false;
        for (Val each : call.args()) {
            givenAFunction |= !each.functions().isEmpty();
        }
        boolean handed = false;
        for (Val each : call.everything()) {
            for (Tag tag : each.tags()) {
                if (tag.isHeld()) {
                    handed = true;
                }
            }
        }
        // A function is run over what the container holds only where the library's function it
        // is given has a row; a function given to anything else is not followed.
        boolean read = givenAFunction ? callbackOf(call).isPresent()
                : understands(call.name(), call.args().size());
        if (handed && !read) {
            for (Val each : call.everything()) {
                for (Tag tag : each.tags()) {
                    if (tag.isHeld()) {
                        out.add(tag.origin());
                    }
                }
            }
        }
        if (storesIntoSomethingUntracked(call)) {
            for (Val each : call.args()) {
                for (Tag tag : each.tags()) {
                    if (tag.kind() == Kind.COLLECTION || tag.isHeld()) {
                        out.add(tag.origin());
                    }
                }
            }
        }
        if (onAWindow(call)) {
            for (Tag said : textOfHeld(call)) {
                out.add(said.origin());
            }
        }
        return out;
    }

    /**
     * Whether the call stores in an object that writes through to another container: the cursor of
     * a list, an entry of a map, a view. What is stored in it is stored in the container it is of
     * as well, and that is not followed.
     *
     * <p>It is known to be one by its tag; and where it was handed in by a caller that did not
     * say, by the type the store is declared on, since a cursor and an entry that nothing here
     * made are views of something.
     */
    private static boolean storesIntoSomethingUntracked(Call call) {
        if (call.isStatic() || call.name().equals("<init>")) {
            return false;
        }
        if (placementOf(call.name(), call.args().size()).isEmpty()
                && !PUTS_ALL.contains(call.name())) {
            return false;
        }
        Val receiver = call.receiver();
        boolean ofSomethingElse = receiver.alloc() < 0
                && (isA(call.owner(), ListIterator.class) || isAnEntry(call.owner()));
        return isAView(receiver) || ofSomethingElse;
    }

    /** The functions the call is given that no row of the table says it runs. */
    static Set<Tag> functionsNotRun(Call call) {
        if (callbackOf(call).isPresent()) {
            return Set.of();
        }
        Set<Tag> out = new LinkedHashSet<>();
        for (Val each : call.args()) {
            out.addAll(each.functions());
        }
        return out;
    }

    /** What the reading says of a call that holds a copy whole and is not followed. */
    static String unresolvedSaid(Call call) {
        String what = call.owner().replace('/', '.') + "." + call.name();
        if (onAWindow(call) && !textOfHeld(call).isEmpty()) {
            return "says a copy held whole into " + what + "'s receiver, which writes to the place"
                    + " it was made over, and what is read there is not followed back";
        }
        return storesIntoSomethingUntracked(call)
                ? "stores a copy whole in " + what + "'s receiver, which is a view of or came from"
                        + " another container, and what is stored there is not followed back"
                : "hands a container that holds a copy whole to " + what + ", and nothing says"
                        + " what that does with the copy";
    }

    // ---- functions

    /**
     * What a copy a function returns is in what the call hands back, as the call says.
     *
     * @param returned what the function returned
     */
    static Set<Tag> handedBackBy(Into into, Set<Tag> returned) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : returned) {
            switch (into) {
                case AS_WALK_ELEMENTS -> out.addAll(asAnElement(each, WALK_ELEMENT));
                case AS_ELEMENTS -> out.addAll(asAnElement(each, ELEMENT));
                case AS_THEY_ARE -> {
                    if (each.isHeld()) {
                        out.add(each);
                    }
                }
                case AS_RETURNED, KEPT_AND_RETURNED -> {
                    if (each.kind() == Kind.COLLECTION || each.isHeld()) {
                        out.add(each);
                    }
                }
                case NOTHING, KEPT_AS_ELEMENTS, KEPT_AS_ARRAY_ELEMENTS -> { }
            }
        }
        return out;
    }

    /**
     * What a copy a function returns is in the container the call was made on, where the call puts
     * the value in it: an element, or a value.
     */
    static Set<Tag> keptBy(Into into, Set<Tag> returned) {
        Set<Tag> out = new LinkedHashSet<>();
        String slot = into == Into.KEPT_AS_ARRAY_ELEMENTS ? ARRAY_ELEMENT : ELEMENT;
        if (into == Into.KEPT_AS_ELEMENTS || into == Into.KEPT_AND_RETURNED
                || into == Into.KEPT_AS_ARRAY_ELEMENTS) {
            for (Tag each : returned) {
                out.addAll(asAnElement(each, slot));
            }
        }
        return out;
    }

    private static Set<Tag> asAnElement(Tag returned, String slot) {
        if (returned.kind() == Kind.COLLECTION) {
            return Set.of(held(returned.origin(), slot));
        }
        return returned.isHeld() ? Set.of(held(returned.origin(), slot + returned.site()))
                : Set.of();
    }

    /** What storing a value in an array of references leaves on the array. */
    static Set<Tag> storedInAnArray(Val value) {
        return putIn(ARRAY_ELEMENT, value);
    }

    /** What loading from an array of references gives: the copies it holds. */
    static Set<Tag> loadedFromAnArray(Val array) {
        return takenOut(held(array), ELEMENTS);
    }

    /**
     * The copies a container holds, as the elements of the functions the call is given: a function
     * handed to a walk over the container is run on each of them, and what it does with one is what
     * is done with the copy. What it returns is an element of what the call hands back where the
     * call maps, and what the container it returns holds where the call spreads.
     */
    private static Feed handedToFunctions(Call call) {
        Optional<Callback> row = callbackOf(call);
        if (row.isEmpty()) {
            return null;
        }
        Callback spec = row.get();
        Set<Tag> functions = call.args().get(spec.function()).functions();
        if (functions.isEmpty()) {
            return null;
        }
        Val container = spec.container() == -1 ? call.receiver()
                : call.args().get(spec.container());
        Set<Tag> held = held(container);
        List<Set<Tag>> elements = new ArrayList<>();
        for (Source each : spec.handed()) {
            elements.add(switch (each) {
                case ELEMENT -> takenOut(held, ELEMENTS);
                case KEY -> takenOut(held, KEY);
                case FIRST_ARGUMENT -> itemsAsTheyAre(call.args().get(0));
                case SECOND_ARGUMENT -> itemsAsTheyAre(call.args().get(1));
            });
        }
        boolean keeps = spec.into() == Into.KEPT_AS_ELEMENTS
                || spec.into() == Into.KEPT_AS_ARRAY_ELEMENTS
                || spec.into() == Into.KEPT_AND_RETURNED;
        return new Feed(functions, elements, false, keeps ? container : null, spec.into());
    }

    // ---- what a call hands back

    /** What the call hands back that holds, or is, a copy taken out of what it is made on. */
    private static Set<Tag> handedBack(Call call) {
        if (call.isStatic()) {
            return madeOf(call);
        }
        String name = call.name();
        if (name.equals("push") && call.args().size() == 1 && call.returnsAReference()) {
            // A stack answers the item it was given, which is what it now holds on top.
            return itemsAsTheyAre(call.args().get(0));
        }
        Set<Tag> held = held(call.receiver());
        if (held.isEmpty() || !call.returnsAReference()) {
            return Set.of();
        }
        if (KEY_VIEWS.contains(name)) {
            return rekeyed(held, ELEMENT);
        }
        if (WALKS_THE_KEYS.contains(name)) {
            return rekeyed(held, WALK_ELEMENT);
        }
        if (VALUE_VIEWS.contains(name)) {
            return takenAlong(held, ELEMENTS);
        }
        if (WALKS_THE_VALUES.contains(name)) {
            return retargeted(takenAlong(held, ELEMENTS), ELEMENTS, WALK_ELEMENT);
        }
        if (ENTRY_VIEWS.contains(name)) {
            return prefixed(held, ELEMENT);
        }
        if (name.equals("peek") && isA(call.owner(), BaseStream.class)) {
            // Looking at each element of a stream as it passes answers the same stream; a queue's
            // peek is the one that answers an element.
            return held;
        }
        if (takesOut(name)) {
            if (call.descriptor().endsWith(")Ljava/util/Optional;")) {
                // An optional of one element holds it as a container does.
                return retargeted(held, ELEMENTS, ELEMENT);
            }
            if (TAKES_AN_ENTRY_OUT.contains(name)) {
                // An entry of a map holds the slots the map does.
                return held;
            }
            return takenOut(held, TAKES_A_KEY_OUT.contains(name) ? KEY : ELEMENTS);
        }
        if (SaltedOrderVocabulary.startsATraversal(name)) {
            // A container and an array walk over what they hold, and a stream is made a cursor over
            // what it was at.
            return retargeted(held, "eaw", WALK_ELEMENT);
        }
        if (name.equals("toList")) {
            return retargeted(held, "aw", ELEMENT);
        }
        if (name.equals("toArray")) {
            return retargeted(held, "ew", ARRAY_ELEMENT);
        }
        if (SaltedOrderVocabulary.isAView(name)
                || SaltedOrderVocabulary.keepsTheElementsOfAWalk(name)
                || SAME_ELEMENTS_IN_ANOTHER_FORM.contains(name)) {
            return held;
        }
        return Set.of();
    }

    /** The copies a value is, or holds, as they are. */
    private static Set<Tag> itemsAsTheyAre(Val value) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : value.tags()) {
            if (each.kind() == Kind.COLLECTION || each.isHeld()) {
                out.add(each);
            }
        }
        return out;
    }

    /** What a call of the library that makes a container, or an element of one, holds. */
    private static Set<Tag> madeOf(Call call) {
        String name = call.name();
        List<Val> args = call.args();
        boolean ofAnArray = !args.isEmpty() && call.descriptor().startsWith("([");
        // What it makes holds what it is given as a stream's elements, or a container's.
        String slot = call.owner().startsWith("java/util/stream/") ? WALK_ELEMENT : ELEMENT;
        Set<Tag> out = new LinkedHashSet<>();
        if (call.owner().equals("java/util/Map") && name.equals("ofEntries") && ofAnArray) {
            // The array holds entries, and an entry holds what a map does.
            out.addAll(takenAlong(held(args.get(0)), ELEMENTS, true));
        } else if (call.owner().equals("java/util/Map") && name.equals("of")) {
            for (int each = 0; each < args.size(); each++) {
                out.addAll(putIn(each % 2 == 0 ? KEY : ELEMENT, args.get(each)));
            }
        } else if (((call.owner().equals("java/util/Map") && name.equals("entry"))
                || name.equals("singletonMap")) && args.size() == 2) {
            out.addAll(putIn(KEY, args.get(0)));
            out.addAll(putIn(ELEMENT, args.get(1)));
        } else if (name.equals("nCopies") && args.size() == 2) {
            out.addAll(putIn(ELEMENT, args.get(1)));
        } else if (ofAnArray && HOLDS_ITS_ARGUMENTS.contains(name)) {
            // A container made of an array holds what the array does, as its elements.
            out.addAll(retargeted(held(args.get(0)), "a", slot));
        } else if (HOLDS_ITS_ARGUMENTS.contains(name)) {
            for (Val each : args) {
                out.addAll(putIn(slot, each));
            }
        } else if (!args.isEmpty() && (name.equals("stream") || name.equals("spliterator")
                || name.equals("enumeration") || call.owner().equals("java/util/Spliterators"))) {
            // A stream over an array, a container or a spliterator walks the same elements, and so
            // does a cursor made of a spliterator, a spliterator made of a cursor or an array, and
            // an enumeration of a container.
            out.addAll(retargeted(held(args.get(0)), "aew", WALK_ELEMENT));
        } else if (!args.isEmpty() && name.equals("list")
                && call.owner().equals("java/util/Collections")) {
            // The list made of an enumeration holds what the enumeration walked.
            out.addAll(retargeted(held(args.get(0)), "w", ELEMENT));
        } else if (!args.isEmpty() && (HANDS_BACK_ITS_ARGUMENT.contains(name)
                || wrapsItsArgument(name))) {
            out.addAll(held(args.get(0)));
        } else if (HANDS_BACK_THE_CONTAINER.contains(name)) {
            // The container it is given, or the elements of both containers it is given.
            for (Val each : args) {
                out.addAll(held(each));
            }
        } else if (!args.isEmpty() && (name.equals("min") || name.equals("max"))
                && call.owner().equals("java/util/Collections")) {
            out.addAll(takenOut(held(args.get(0)), ELEMENTS));
        }
        return out;
    }

    /** What the call puts in the container it is made on. */
    private static Set<Tag> put(Call call) {
        if (call.isStatic()) {
            return Set.of();
        }
        String name = call.name();
        List<Val> args = call.args();
        Set<Tag> out = new LinkedHashSet<>();
        if (name.equals("<init>")) {
            if (isAnEntry(call.owner()) && args.size() == 2) {
                out.addAll(putIn(KEY, args.get(0)));
                out.addAll(putIn(ELEMENT, args.get(1)));
            } else if (args.size() == 1) {
                // A container made of another holds what the other held.
                out.addAll(held(args.get(0)));
            }
            return out;
        }
        if (PUTS_ALL.contains(name) && !args.isEmpty()) {
            out.addAll(held(args.get(args.size() - 1)));
            return out;
        }
        Optional<Placement> where = placementOf(name, args.size());
        if (where.isPresent()) {
            if (where.get().key() != Placement.NONE) {
                out.addAll(putIn(KEY, args.get(where.get().key())));
            }
            out.addAll(putIn(ELEMENT, args.get(where.get().value())));
        }
        return out;
    }

    // ---- paths

    /** The copies this value holds whole, which is the tags that say so. */
    private static Set<Tag> held(Val value) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : value.tags()) {
            if (each.isHeld()) {
                out.add(each);
            }
        }
        return out;
    }

    /** A held copy at this path, widened where the path is longer than the reading follows. */
    private static Tag held(String origin, String path) {
        return Tag.held(origin, widened(path));
    }

    /** The path, or its first slots and {@code *} where it names more than {@link #MAX_DEPTH}. */
    static String widened(String path) {
        boolean any = path.endsWith(ANY);
        String slots = any ? path.substring(0, path.length() - 1) : path;
        return slots.length() <= MAX_DEPTH ? path : slots.substring(0, MAX_DEPTH) + ANY;
    }

    /** What putting this value in one slot of a container leaves on the container. */
    private static Set<Tag> putIn(String slot, Val value) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : value.tags()) {
            if (each.kind() == Kind.COLLECTION) {
                out.add(held(each.origin(), slot));
            } else if (each.isHeld()) {
                out.add(held(each.origin(), slot + each.site()));
            }
        }
        return out;
    }

    /**
     * What is taken out of one of these slots: the copy itself where nothing is left of the path,
     * and what the copy's own slots hold where something is. Where what is left is {@code *} it is
     * both, for the copy may be that slot or deeper.
     */
    private static Set<Tag> takenOut(Set<Tag> held, String slots) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            String rest = restAfter(each, slots);
            if (rest == null) {
                continue;
            }
            if (rest.isEmpty()) {
                out.add(new Tag(Kind.COLLECTION, each.origin()));
            } else if (rest.equals(ANY)) {
                out.add(new Tag(Kind.COLLECTION, each.origin()));
                out.add(held(each.origin(), ANY));
            } else {
                out.add(held(each.origin(), rest));
            }
        }
        return out;
    }

    /** What is left of the path once a slot of these is taken, or null where it is another's. */
    private static String restAfter(Tag held, String slots) {
        if (held.site().equals(ANY)) {
            return ANY;
        }
        return !held.site().isEmpty() && slots.contains(held.site().substring(0, 1))
                ? held.site().substring(1) : null;
    }

    /**
     * The same copies with the first slot of the paths that begin with one of {@code from} changed
     * to {@code to}: what a stream over a container holds is what the container did, as the
     * elements of a walk.
     */
    private static Set<Tag> retargeted(Set<Tag> held, String from, String to) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            if (each.site().equals(ANY)) {
                out.add(each);
            } else if (!each.site().isEmpty() && from.contains(each.site().substring(0, 1))) {
                out.add(held(each.origin(), to + each.site().substring(1)));
            }
        }
        return out;
    }

    /** What a view of the elements holds: the same, as elements of the view. */
    private static Set<Tag> takenAlong(Set<Tag> held, String slots) {
        return takenAlong(held, slots, false);
    }

    /**
     * The tags a slot holds, kept as they are, or with the slot taken off where {@code strip} says
     * the elements are themselves containers whose slots are what is wanted.
     */
    private static Set<Tag> takenAlong(Set<Tag> held, String slots, boolean strip) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            String rest = restAfter(each, slots);
            if (rest == null) {
                continue;
            }
            if (!strip) {
                out.add(each);
            } else if (rest.equals(ANY)) {
                out.add(held(each.origin(), ANY));
            } else if (!rest.isEmpty()) {
                out.add(held(each.origin(), rest));
            }
        }
        return out;
    }

    /** What the keys of a map are, as the elements of a set or a walk. */
    private static Set<Tag> rekeyed(Set<Tag> held, String as) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            String rest = restAfter(each, KEY);
            if (rest == null) {
                continue;
            }
            out.add(each.site().equals(ANY) ? each : held(each.origin(), as + rest));
        }
        return out;
    }

    /** What a set of the entries of a map holds: what the map holds, one slot further in. */
    private static Set<Tag> prefixed(Set<Tag> held, String slot) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            out.add(held(each.origin(), slot + each.site()));
        }
        return out;
    }

    /** How many slots the longest path among these names, for the reading to say. */
    static int longestPath(Set<Tag> tags) {
        int longest = 0;
        for (Tag each : tags) {
            if (each.isHeld()) {
                longest = Math.max(longest, each.site().length());
            }
        }
        return longest;
    }

    /**
     * Whether the call of this name with this many arguments writes what it holds into the
     * container or array it is given, which is not the one it answers: where it has room it fills
     * the array it is given, and whether it has is not asked.
     */
    static boolean writesIntoItsArgument(String name, int arity) {
        return STORES_WHAT_IT_HOLDS_IN_ITS_ARGUMENT.contains(name)
                || (name.equals("toArray") && arity == 1);
    }

    /**
     * Whether a static call of the library writes into one of the containers or arrays it is
     * given: the copies of one into another, a fill, an array copy.
     */
    static boolean writesIntoItsArgument(String owner, String name, int arity) {
        return switch (owner) {
            case "java/lang/System" -> name.equals("arraycopy") && arity == 5;
            case "java/util/Collections" -> (name.equals("addAll") && arity == 2)
                    || (name.equals("copy") && arity == 2) || (name.equals("fill") && arity == 2)
                    || (name.equals("replaceAll") && arity == 3);
            case "java/util/Arrays" -> (name.equals("fill") && arity >= 2)
                    || (name.equals("setAll") && arity == 2);
            default -> false;
        };
    }

    /** The descriptor's argument count, for a table that is read by arity. */
    static int arityOf(String descriptor) {
        return MethodTypeDesc.ofDescriptor(descriptor).parameterCount();
    }
}
