package souther.bench;

import souther.bench.SaltedOrder.Kind;
import souther.bench.SaltedOrder.Tag;
import souther.bench.SaltedOrder.Val;
import souther.bench.SaltedOrderVocabulary.Call;
import souther.bench.SaltedOrderVocabulary.Feed;
import souther.bench.SaltedOrderVocabulary.Outcome;
import souther.bench.SaltedOrderVocabulary.Push;

import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * What a call does to the copies a container holds whole.
 *
 * <p>A copy put into a list, or beside a key of a map, leaves the order of the container where it
 * was: the container's order is the order things were put in, and holds nothing of how the copy
 * iterates. What changes is what can be taken out of it, so the container carries, for each copy,
 * a {@link Kind#HELD} tag whose site is the path of slots down to it: {@code e} for an element or a
 * value, {@code k} for a key, outermost first. A list of lists of copies says {@code ee}, and a map
 * from a copy to anything says {@code k}.
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
 *
 * <p><b>A container that holds a copy is never handed to something unread in silence.</b> What a
 * call does with one is a word of this table (it stores, takes out, makes a view or a copy, clears,
 * asks only what is held, runs a function over it, makes text) or it is said so as a finding that
 * names the copy. The text of a container says the copies it holds in the order they iterate. A
 * view, a cursor or an entry of another container writes through to it, which is not followed: what
 * is stored in one is said so as well, since it is stored in the container it is of.
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
 * <p>The text of a container is the text of what it holds; an array, a stream and a cursor name
 * themselves and say nothing of their elements.
 */
final class HeldCopies {

    /** The most slots a path names before it is widened. */
    static final int MAX_DEPTH = 3;

    private static final String ANY = "*";

    private static final String ELEMENT = "e";

    private static final String KEY = "k";

    /** What an array is made as, by the instruction that makes one. */
    private static final String ARRAY = "array";

    /**
     * Where what a function returns goes, in the call that was given the function: nowhere, as a
     * predicate's answer does; an element of what the call hands back, as the function of a
     * {@code map} makes one; what the container the function returned held, as a {@code flatMap}
     * spreads it; what the call hands back as it is, as a supplier's does; an element of the
     * container the call is made on, as a {@code replaceAll} puts it; or both of those last two,
     * as a {@code compute} puts the value in the map and answers it.
     */
    enum Into {
        NOTHING,
        AS_ELEMENTS,
        AS_THEY_ARE,
        AS_RETURNED,
        KEPT_AS_ELEMENTS,
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

    /** Which kinds of container a row is about: a map hands a function a key as well. */
    private enum On {
        ANY,
        MAPS,
        THE_REST
    }

    /**
     * What the call of this name with this many arguments does with a function it is given.
     *
     * @param function  which argument is the function
     * @param container which argument is the container the function is run over: -1 is the one the
     *                  call is made on
     * @param on        the kind of container the row is about
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
            "shuffle", "sort", "elementCount", "remainingCapacity", "empty", "mappingCount");

    /** What makes text of what it is handed, so that a container says the copies it holds. */
    private static final Set<String> MAKES_TEXT_OF_ITS_ARGUMENTS = Set.of(
            "valueOf", "format", "formatted", "append", "insert", "print", "println", "toString");

    /** What hands back the container it is given, or one that holds what it did. */
    private static final Set<String> HANDS_BACK_THE_CONTAINER = Set.of(
            "requireNonNull", "requireNonNullElse", "requireNonNullElseGet", "concat");

    /** What stores what it holds in a container it is given. */
    private static final Set<String> STORES_WHAT_IT_HOLDS_IN_ITS_ARGUMENT = Set.of(
            "drainTo", "copyInto");

    private static final Set<String> KEY_VIEWS = Set.of(
            "keySet", "sequencedKeySet", "navigableKeySet", "descendingKeySet", "keys");

    private static final Set<String> VALUE_VIEWS = Set.of(
            "values", "sequencedValues", "elements");

    private static final Set<String> ENTRY_VIEWS = Set.of("entrySet", "sequencedEntrySet");

    private static final Set<String> HOLDS_ITS_ARGUMENTS = Set.of(
            "of", "asList", "singleton", "singletonList", "ofNullable");

    private static final Set<String> HANDS_BACK_ITS_ARGUMENT = Set.of(
            "copyOf", "copyOfRange", "stream");

    private static final Set<String> SAME_ELEMENTS_IN_ANOTHER_FORM = Set.of(
            "toList", "toArray", "sorted", "clone", "asIterator");

    private HeldCopies() {}

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
        out.add(new Callback("forEach", 1, 0, -1, On.THE_REST, element, Into.NOTHING));
        out.add(new Callback("forEach", 1, 0, -1, On.MAPS, keyAndValue, Into.NOTHING));
        for (String name : List.of("forEachRemaining", "forEachOrdered", "removeIf", "ifPresent",
                "filter", "peek", "takeWhile", "dropWhile", "anyMatch", "allMatch", "noneMatch")) {
            out.add(new Callback(name, 1, 0, -1, On.ANY, element, Into.NOTHING));
        }
        out.add(new Callback("ifPresentOrElse", 2, 0, -1, On.ANY, element, Into.NOTHING));
        out.add(new Callback("replaceAll", 1, 0, -1, On.THE_REST, element,
                Into.KEPT_AS_ELEMENTS));
        out.add(new Callback("replaceAll", 1, 0, -1, On.MAPS, keyAndValue,
                Into.KEPT_AS_ELEMENTS));
        for (String name : List.of("sort", "sorted", "min", "max")) {
            out.add(new Callback(name, 1, 0, -1, On.ANY, two, Into.NOTHING));
        }
        out.add(new Callback("reduce", 1, 0, -1, On.ANY, two, Into.AS_ELEMENTS));
        out.add(new Callback("reduce", 2, 1, -1, On.ANY, two, Into.AS_RETURNED));
        for (String name : List.of("map", "mapToObj")) {
            out.add(new Callback(name, 1, 0, -1, On.ANY, element, Into.AS_ELEMENTS));
        }
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
        out.add(new Callback("generate", 1, 0, -1, On.ANY, List.of(), Into.AS_ELEMENTS));
        for (String name : List.of("sort", "max", "min")) {
            out.add(new Callback(name, 2, 1, 0, On.ANY, two, Into.NOTHING));
        }
        out.add(new Callback("sort", 4, 3, 0, On.ANY, two, Into.NOTHING));
        out.add(new Callback("setAll", 2, 1, 0, On.ANY, List.of(), Into.KEPT_AS_ELEMENTS));
        return out;
    }

    /** The row for this call, if the library's function it is given has one. */
    private static Optional<Callback> callbackOf(Call call) {
        boolean ofAMap = call.owner().endsWith("Map");
        for (Callback each : CALLBACKS) {
            boolean kind = each.on() == On.ANY || (each.on() == On.MAPS) == ofAMap;
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

    private static void row(Map<String, Map<Integer, Placement>> into, String name, int arity,
                            int key, int value) {
        into.computeIfAbsent(name, each -> new HashMap<>()).put(arity, new Placement(key, value));
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
        return name.equals("getKey") || SaltedOrderVocabulary.takesOneOut(name)
                || TAKES_THE_ONLY_ONE_OUT.contains(name);
    }

    /** What the call does to held copies, joined to what the order reading made of it. */
    static Outcome through(Call call, Outcome order) {
        Outcome out = withText(call, order);
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
        return markedAsAWalk(call, markedAsAView(call, out));
    }

    /**
     * What a call answers that is a stream or a cursor is marked, by the type it is declared to
     * answer and not by its name, so that its text is known to be its own name.
     */
    private static Outcome markedAsAWalk(Call call, Outcome out) {
        String returns = call.descriptor().substring(call.descriptor().indexOf(')') + 1);
        boolean walk = (returns.startsWith("Ljava/util/stream/") && returns.endsWith("Stream;"))
                || returns.equals("Ljava/util/Iterator;")
                || returns.equals("Ljava/util/ListIterator;")
                || returns.equals("Ljava/util/Enumeration;")
                || returns.equals("Ljava/util/Spliterator;");
        if (!walk) {
            return out;
        }
        return new Outcome(out.result().withMade(Val.A_WALK), out.pushes(), out.clears(),
                out.feeds(), out.crossedBy(), out.unmodeled(), out.endsAs());
    }

    /**
     * What a call answers that writes through to the container it was made on is marked, so that a
     * put to it is known not to reach any object that is tracked. The entries of a map are views of
     * it, and so is the cursor of a list, a key set, a sublist; what is taken out of the entries of
     * a map is an entry.
     */
    private static Outcome markedAsAView(Call call, Outcome out) {
        if (call.isStatic() || !call.returnsAReference()) {
            return out;
        }
        String name = call.name();
        int mark;
        if (call.receiver().isEntries()) {
            if (takesOut(name) && !name.endsWith("Key")) {
                mark = Val.A_VIEW;
            } else if (SaltedOrderVocabulary.keepsTheElementsOfAWalk(name)
                    || SaltedOrderVocabulary.isAView(name)) {
                mark = Val.ENTRIES;
            } else {
                return out;
            }
        } else if (ENTRY_VIEWS.contains(name)) {
            mark = Val.ENTRIES;
        } else if (KEY_VIEWS.contains(name) || VALUE_VIEWS.contains(name)
                || SaltedOrderVocabulary.isAView(name) || name.equals("listIterator")) {
            mark = Val.A_VIEW;
        } else {
            return out;
        }
        return new Outcome(out.result().withAlloc(mark), out.pushes(), out.clears(), out.feeds(),
                out.crossedBy(), out.unmodeled(), out.endsAs());
    }

    /** The text a call makes of the containers it is handed says the copies they hold, in order. */
    private static Outcome withText(Call call, Outcome order) {
        Set<Tag> said = textOfHeld(call);
        if (said.isEmpty()) {
            return order;
        }
        Outcome out = order;
        boolean intoABuilder = !call.isStatic()
                && (call.name().equals("append") || call.name().equals("insert"));
        if (intoABuilder) {
            out = SaltedOrderVocabulary.alsoPushing(out, List.of(new Push(call.receiver(), said)));
        }
        return call.returnsAReference() ? out.holding(said) : out;
    }

    /**
     * The order each copy held in what the call is handed is said in, where the call makes text of
     * it. The text of a container is the text of what it holds, and a set that is a copy says its
     * elements in the order it iterates.
     */
    static Set<Tag> textOfHeld(Call call) {
        String name = call.name();
        boolean ofTheReceiver = name.equals("toString") && !call.isStatic()
                && call.args().isEmpty();
        if (!ofTheReceiver && !MAKES_TEXT_OF_ITS_ARGUMENTS.contains(name)) {
            return Set.of();
        }
        // Only these say the elements of an array: the text of an array is its own name.
        boolean elementsOfAnArray = call.isStatic() && call.owner().equals("java/util/Arrays")
                && (name.equals("toString") || name.equals("deepToString"));
        Set<Tag> out = new LinkedHashSet<>();
        for (Val each : call.args()) {
            addTextOf(each, out, elementsOfAnArray);
        }
        if (ofTheReceiver) {
            addTextOf(call.receiver(), out, false);
        }
        return out;
    }

    /**
     * Whether the text of this is what it is and not what it holds: a stream and a cursor name
     * themselves, and so does an array. Which it is was settled where it was made, by what the call
     * that made it was declared to answer.
     */
    static boolean namesItself(Val value) {
        return ARRAY.equals(value.made()) || Val.A_WALK.equals(value.made());
    }

    private static void addTextOf(Val value, Set<Tag> into, boolean arrayIsItsElements) {
        boolean saysWhatItHolds = !namesItself(value)
                || (arrayIsItsElements && ARRAY.equals(value.made()));
        if (!saysWhatItHolds) {
            return;
        }
        for (Tag each : value.tags()) {
            if (each.isHeld()) {
                into.add(new Tag(Kind.SEQUENCE, each.origin()));
            }
        }
    }

    /** What the call puts in the containers it is given, which are not the one it is made on. */
    private static List<Push> putIntoArguments(Call call) {
        String name = call.name();
        List<Val> args = call.args();
        String owner = call.owner();
        if (!call.isStatic()) {
            // What a container holds is put in the one it is given.
            return STORES_WHAT_IT_HOLDS_IN_ITS_ARGUMENT.contains(name) && !args.isEmpty()
                    ? pushed(args.get(0), held(call.receiver())) : List.of();
        }
        if (owner.equals("java/lang/System") && name.equals("arraycopy") && args.size() == 5) {
            return pushed(args.get(2), held(args.get(0)));
        }
        if (owner.equals("java/util/Collections")) {
            if (name.equals("addAll") && args.size() == 2) {
                return pushed(args.get(0), held(args.get(1)));
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
            return pushed(args.get(0), putIn(ELEMENT, args.get(args.size() - 1)));
        }
        return List.of();
    }

    private static List<Push> pushed(Val into, Set<Tag> tags) {
        return tags.isEmpty() ? List.of() : List.of(new Push(into, tags));
    }

    /**
     * Whether the operation of this name is one this reads, for a container that holds a copy: it
     * stores, takes out, makes a view or a copy, clears, asks only what is held, or makes text.
     * What is none of those is not followed, and is said so when a container that holds a copy is
     * handed to it.
     */
    static boolean understands(String name, int arity) {
        return placementOf(name, arity).isPresent() || PUTS_ALL.contains(name)
                || takesOut(name) || KEY_VIEWS.contains(name) || VALUE_VIEWS.contains(name)
                || ENTRY_VIEWS.contains(name) || SaltedOrderVocabulary.isAView(name)
                || SaltedOrderVocabulary.keepsTheElementsOfAWalk(name)
                || SAME_ELEMENTS_IN_ANOTHER_FORM.contains(name) || name.equals("clear")
                || name.equals("<init>") || ASKS_ONLY.contains(name)
                || hasACallback(name, arity)
                || STORES_WHAT_IT_HOLDS_IN_ITS_ARGUMENT.contains(name)
                || (name.equals("search") && arity <= 2)
                || MAKES_TEXT_OF_ITS_ARGUMENTS.contains(name)
                || HOLDS_ITS_ARGUMENTS.contains(name) || HANDS_BACK_ITS_ARGUMENT.contains(name)
                || HANDS_BACK_THE_CONTAINER.contains(name)
                || name.startsWith("unmodifiable") || name.startsWith("synchronized")
                || name.startsWith("checked") || name.equals("entry")
                || name.equals("singletonMap") || name.equals("nCopies")
                || name.equals("ofEntries") || name.equals("arraycopy")
                || name.equals("fill") || name.equals("copy") || name.equals("replaceAll");
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
        return out;
    }

    /**
     * Whether the call stores in an object that nothing here made or holds in a place: the cursor of
     * a list, an entry of a map, a view, what a call of something that is not read answered. What
     * is stored in it is stored in the container it is of as well, and that is not followed.
     */
    private static boolean storesIntoSomethingUntracked(Call call) {
        if (call.isStatic() || call.name().equals("<init>")) {
            return false;
        }
        if (placementOf(call.name(), call.args().size()).isEmpty()
                && !PUTS_ALL.contains(call.name())) {
            return false;
        }
        return call.receiver().isAView();
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
        return storesIntoSomethingUntracked(call)
                ? "stores a copy whole in " + what + "'s receiver, which is a view of or came from"
                        + " another container, and what is stored there is not followed back"
                : "hands a container that holds a copy whole to " + what + ", and nothing says"
                        + " what that does with the copy";
    }

    /**
     * What a copy a function returns is in what the call hands back, as the call says.
     *
     * @param returned what the function returned
     */
    static Set<Tag> handedBackBy(Into into, Set<Tag> returned) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : returned) {
            switch (into) {
                case AS_ELEMENTS -> out.addAll(asAnElement(each));
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
                case NOTHING, KEPT_AS_ELEMENTS -> { }
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
        if (into == Into.KEPT_AS_ELEMENTS || into == Into.KEPT_AND_RETURNED) {
            for (Tag each : returned) {
                out.addAll(asAnElement(each));
            }
        }
        return out;
    }

    private static Set<Tag> asAnElement(Tag returned) {
        if (returned.kind() == Kind.COLLECTION) {
            return Set.of(held(returned.origin(), ELEMENT));
        }
        return returned.isHeld() ? Set.of(held(returned.origin(), ELEMENT + returned.site()))
                : Set.of();
    }

    /** What storing a value in an array of references leaves on the array. */
    static Set<Tag> storedInAnArray(Val value) {
        return putIn(ELEMENT, value);
    }

    /** What loading from an array of references gives: the copies it holds. */
    static Set<Tag> loadedFromAnArray(Val array) {
        return takenOut(held(array), ELEMENT);
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
                case ELEMENT -> takenOut(held, ELEMENT);
                case KEY -> takenOut(held, KEY);
                case FIRST_ARGUMENT -> itemsAsTheyAre(call.args().get(0));
                case SECOND_ARGUMENT -> itemsAsTheyAre(call.args().get(1));
            });
        }
        boolean keeps = spec.into() == Into.KEPT_AS_ELEMENTS
                || spec.into() == Into.KEPT_AND_RETURNED;
        return new Feed(functions, elements, false, keeps ? container : null, spec.into());
    }

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
            return rekeyed(held);
        }
        if (VALUE_VIEWS.contains(name)) {
            return takenAlong(held, ELEMENT);
        }
        if (ENTRY_VIEWS.contains(name)) {
            return prefixed(held, ELEMENT);
        }
        if (takesOut(name)) {
            if (call.descriptor().endsWith(")Ljava/util/Optional;") || name.endsWith("Entry")) {
                // An optional of one element holds the slot its elements are in, and so does an
                // entry of a map.
                return held;
            }
            return takenOut(held, name.endsWith("Key") || name.equals("getKey") ? KEY : ELEMENT);
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
        Set<Tag> out = new LinkedHashSet<>();
        if (call.owner().equals("java/util/Map") && name.equals("ofEntries") && ofAnArray) {
            // The array holds entries, and an entry holds what a map does.
            out.addAll(takenAlong(held(args.get(0)), ELEMENT, true));
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
        } else if (ofAnArray && (HOLDS_ITS_ARGUMENTS.contains(name)
                || HANDS_BACK_ITS_ARGUMENT.contains(name))) {
            // A container made of an array holds what the array does, in the same slot.
            out.addAll(held(args.get(0)));
        } else if (HOLDS_ITS_ARGUMENTS.contains(name)) {
            for (Val each : args) {
                out.addAll(putIn(ELEMENT, each));
            }
        } else if (!args.isEmpty() && (HANDS_BACK_ITS_ARGUMENT.contains(name)
                || name.startsWith("unmodifiable") || name.startsWith("synchronized")
                || name.startsWith("checked"))) {
            out.addAll(held(args.get(0)));
        } else if (HANDS_BACK_THE_CONTAINER.contains(name)) {
            // The container it is given, or the elements of both containers it is given.
            for (Val each : args) {
                out.addAll(held(each));
            }
        } else if (!args.isEmpty() && (name.equals("min") || name.equals("max"))
                && call.owner().equals("java/util/Collections")) {
            out.addAll(takenOut(held(args.get(0)), ELEMENT));
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
            if (call.owner().startsWith("java/util/AbstractMap$Simple") && args.size() == 2) {
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
     * What is taken out of one slot: the copy itself where nothing is left of the path, and what
     * the copy's own slots hold where something is. Where what is left is {@code *} it is both, for
     * the copy may be that slot or deeper.
     */
    private static Set<Tag> takenOut(Set<Tag> held, String slot) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            String rest = restAfter(each, slot);
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

    /** What is left of the path once this slot is taken, or null where it is another slot's. */
    private static String restAfter(Tag held, String slot) {
        if (held.site().equals(ANY)) {
            return ANY;
        }
        return held.site().startsWith(slot) ? held.site().substring(slot.length()) : null;
    }

    /** What a view of the elements of a slot holds: the same, as elements of the view. */
    private static Set<Tag> takenAlong(Set<Tag> held, String slot) {
        return takenAlong(held, slot, false);
    }

    /**
     * The tags a slot holds, kept as they are, or with the slot taken off where {@code strip} says
     * the elements are themselves containers whose slots are what is wanted.
     */
    private static Set<Tag> takenAlong(Set<Tag> held, String slot, boolean strip) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            String rest = restAfter(each, slot);
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

    /** What the keys of a map are, as the elements of a set. */
    private static Set<Tag> rekeyed(Set<Tag> held) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            String rest = restAfter(each, KEY);
            if (rest == null) {
                continue;
            }
            out.add(each.site().equals(ANY) ? each : held(each.origin(), ELEMENT + rest));
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

    /** The descriptor's argument count, for a table that is read by arity. */
    static int arityOf(String descriptor) {
        return MethodTypeDesc.ofDescriptor(descriptor).parameterCount();
    }
}
