package souther.bench;

import souther.bench.SaltedOrder.Kind;
import souther.bench.SaltedOrder.Tag;
import souther.bench.SaltedOrder.Val;
import souther.bench.SaltedOrderVocabulary.Call;
import souther.bench.SaltedOrderVocabulary.Feed;
import souther.bench.SaltedOrderVocabulary.Outcome;
import souther.bench.SaltedOrderVocabulary.Push;

import java.lang.constant.MethodTypeDesc;
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
 * <p><b>What this does not follow.</b> A container is a set of paths and not of keys, so a put to
 * a key a copy was put to before does not take the copy out: that is read as holding both, which
 * says more than the code does. {@code clear} is the only operation that takes something out. A
 * function that makes the value a map keeps, and a copy handed to {@code System.arraycopy}, are not
 * followed either. A copy that is only held and never read by anything that takes it out ends
 * nowhere, and the test that asks where every copy ends is what says so.
 */
final class HeldCopies {

    /** The most slots a path names before it is widened. */
    static final int MAX_DEPTH = 3;

    private static final String ANY = "*";

    private static final String ELEMENT = "e";

    private static final String KEY = "k";

    /**
     * What a copy a function returns becomes in what the call that was given the function hands
     * back: an element of it, as the function of a {@code map} makes one, or what the container the
     * function returned held, as a {@code flatMap} spreads it.
     */
    enum Into {
        NOTHING,
        AS_ELEMENTS,
        AS_THEY_ARE
    }

    /** Where, among a call's arguments, the key and the value it stores are; none is -1. */
    record Placement(int key, int value) {

        static final int NONE = -1;
    }

    private static final Map<String, Map<Integer, Placement>> PLACEMENTS = placements();

    private static final Set<String> PUTS_ALL = Set.of("addAll", "putAll", "addAllAbsent");

    private static final Set<String> STORES_WHAT_A_FUNCTION_MAKES = Set.of(
            "compute", "computeIfAbsent", "computeIfPresent", "replaceAll");

    /** What takes the one value out that a container holds, or hands the one it held back. */
    private static final Set<String> TAKES_THE_ONLY_ONE_OUT = Set.of(
            "get", "getOrDefault", "remove", "orElse", "orElseGet", "orElseThrow", "getValue",
            "firstElement", "lastElement", "take", "takeFirst", "takeLast", "put", "putIfAbsent",
            "replace", "set", "merge", "compute", "computeIfAbsent", "computeIfPresent",
            "putFirst", "putLast", "push");

    private static final Set<String> KEY_VIEWS = Set.of("keySet", "sequencedKeySet");

    private static final Set<String> VALUE_VIEWS = Set.of("values", "sequencedValues");

    private static final Set<String> ENTRY_VIEWS = Set.of("entrySet", "sequencedEntrySet");

    private static final Set<String> HOLDS_ITS_ARGUMENTS = Set.of(
            "of", "asList", "singleton", "singletonList", "ofNullable");

    private static final Set<String> HANDS_BACK_ITS_ARGUMENT = Set.of(
            "copyOf", "copyOfRange", "stream");

    private static final Set<String> SAME_ELEMENTS_IN_ANOTHER_FORM = Set.of(
            "toList", "toArray", "sorted", "clone");

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

    /** Whether the call stores what a function it is given makes, which is not followed. */
    static boolean storesWhatAFunctionMakes(String name) {
        return STORES_WHAT_A_FUNCTION_MAKES.contains(name);
    }

    /** Whether the call of this name hands back a value, a key or an element a container held. */
    static boolean takesOut(String name) {
        return name.equals("getKey") || SaltedOrderVocabulary.takesOneOut(name)
                || TAKES_THE_ONLY_ONE_OUT.contains(name);
    }

    /** What the call does to held copies, joined to what the order reading made of it. */
    static Outcome through(Call call, Outcome order) {
        if (!SaltedOrderVocabulary.inTheCollectionsLibrary(call.owner())) {
            return order;
        }
        Outcome out = order;
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
        return out;
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
                case AS_ELEMENTS -> {
                    if (each.kind() == Kind.COLLECTION) {
                        out.add(held(each.origin(), ELEMENT));
                    } else if (each.isHeld()) {
                        out.add(held(each.origin(), ELEMENT + each.site()));
                    }
                }
                case AS_THEY_ARE -> {
                    if (each.isHeld()) {
                        out.add(each);
                    }
                }
                case NOTHING -> { }
            }
        }
        return out;
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
        Set<Tag> functions = new LinkedHashSet<>();
        for (Val each : call.args()) {
            functions.addAll(each.functions());
        }
        Set<Tag> held = held(call.receiver());
        if (functions.isEmpty() || held.isEmpty() || call.isStatic()) {
            return null;
        }
        boolean keyedToo = call.owner().endsWith("Map") && call.name().equals("forEach");
        List<Set<Tag>> elements = keyedToo
                ? List.of(takenOut(held, KEY), takenOut(held, ELEMENT))
                : List.of(takenOut(held, ELEMENT));
        Into into = switch (call.name()) {
            case "map", "mapToObj" -> Into.AS_ELEMENTS;
            case "flatMap" -> Into.AS_THEY_ARE;
            default -> Into.NOTHING;
        };
        return new Feed(functions, elements, false, null, into);
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
                || name.startsWith("unmodifiable") || name.startsWith("synchronized"))) {
            out.addAll(held(args.get(0)));
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
