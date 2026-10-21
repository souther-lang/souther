package souther.bench;

import souther.bench.SaltedOrder.Kind;
import souther.bench.SaltedOrder.Tag;
import souther.bench.SaltedOrder.Val;
import souther.bench.SaltedOrderVocabulary.Call;
import souther.bench.SaltedOrderVocabulary.Feed;
import souther.bench.SaltedOrderVocabulary.Outcome;
import souther.bench.SaltedOrderVocabulary.Push;

import java.util.LinkedHashSet;
import java.util.List;
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
 * <p>A path is all a container carries, so nothing is made per element or per call. What takes
 * something out says which slot, and the tag becomes the copy itself where the path is spent and
 * stays a held one where it is not. That is one table, here, and it is joined to what the order
 * reading says of the same call and does not stand in for it: a container can hold a copy and be
 * made of another's elements at once, and each is read.
 *
 * <p>Held copies are followed where the code follows them and are said to be lost where it does
 * not. A container that is changed other than by the operations below, a function that is handed
 * its elements, or an array, does not carry them on; the reading of a copy that is only held, and
 * never read by anything that takes it out, ends nowhere, and the test that asks where every copy
 * ends is what says so.
 */
final class HeldCopies {

    private static final String ELEMENT = "e";

    private static final String KEY = "k";

    private static final Set<String> PUTS_AN_ELEMENT = Set.of(
            "add", "addFirst", "addLast", "push", "offer", "offerFirst", "offerLast", "set",
            "addElement", "insertElementAt");

    private static final Set<String> PUTS_A_KEY_AND_A_VALUE = Set.of(
            "put", "putIfAbsent", "putFirst", "putLast", "merge");

    private static final Set<String> PUTS_ALL = Set.of("addAll", "putAll");

    private static final Set<String> TAKES_THE_ONLY_ONE_OUT = Set.of(
            "get", "getOrDefault", "remove", "orElse", "orElseGet", "orElseThrow");

    private static final Set<String> KEY_VIEWS = Set.of("keySet", "sequencedKeySet");

    private static final Set<String> VALUE_VIEWS = Set.of("values", "sequencedValues");

    private static final Set<String> ENTRY_VIEWS = Set.of("entrySet", "sequencedEntrySet");

    private static final Set<String> HOLDS_ITS_ARGUMENTS = Set.of(
            "of", "asList", "singleton", "singletonList", "ofNullable");

    private static final Set<String> HANDS_BACK_ITS_ARGUMENT = Set.of("copyOf");

    private static final Set<String> SAME_ELEMENTS_IN_ANOTHER_FORM = Set.of(
            "toList", "toArray", "sorted");

    private HeldCopies() {}

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
     * The copies a container holds, as the elements of the functions the call is given: a function
     * handed to a walk over the container is run on each of them, and what it does with one is what
     * is done with the copy.
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
        return new Feed(functions, elements, false);
    }

    /** What the call hands back that holds, or is, a copy taken out of what it is made on. */
    private static Set<Tag> handedBack(Call call) {
        if (call.isStatic()) {
            return madeOf(call);
        }
        Set<Tag> held = held(call.receiver());
        if (held.isEmpty() || !call.returnsAReference()) {
            return Set.of();
        }
        String name = call.name();
        if (name.equals("getKey")) {
            return takenOut(held, KEY);
        }
        if (name.equals("getValue")) {
            return takenOut(held, ELEMENT);
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
        if (SaltedOrderVocabulary.takesOneOut(name) || TAKES_THE_ONLY_ONE_OUT.contains(name)) {
            if (call.descriptor().endsWith(")Ljava/util/Optional;") || name.endsWith("Entry")) {
                // An optional of one element holds the slot its elements are in, and so does an
                // entry of a map.
                return held;
            }
            return takenOut(held, name.endsWith("Key") ? KEY : ELEMENT);
        }
        if (SaltedOrderVocabulary.isAView(name)
                || SaltedOrderVocabulary.keepsTheElementsOfAWalk(name)
                || SAME_ELEMENTS_IN_ANOTHER_FORM.contains(name)) {
            return held;
        }
        return Set.of();
    }

    /** What a call of the library that makes a container, or an element of one, holds. */
    private static Set<Tag> madeOf(Call call) {
        String name = call.name();
        List<Val> args = call.args();
        Set<Tag> out = new LinkedHashSet<>();
        if (call.owner().equals("java/util/Map") && name.equals("of")) {
            for (int each = 0; each < args.size(); each++) {
                out.addAll(putIn(each % 2 == 0 ? KEY : ELEMENT, args.get(each)));
            }
        } else if (call.owner().equals("java/util/Map") && name.equals("entry")
                && args.size() == 2) {
            out.addAll(putIn(KEY, args.get(0)));
            out.addAll(putIn(ELEMENT, args.get(1)));
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
        boolean aPair = call.owner().startsWith("java/util/AbstractMap$Simple");
        if (name.equals("<init>")) {
            if (aPair && args.size() == 2) {
                out.addAll(putIn(KEY, args.get(0)));
                out.addAll(putIn(ELEMENT, args.get(1)));
            } else if (args.size() == 1) {
                // A container made of another holds what the other held.
                out.addAll(held(args.get(0)));
            }
        } else if (PUTS_AN_ELEMENT.contains(name) && !args.isEmpty()) {
            out.addAll(putIn(ELEMENT, args.get(args.size() - 1)));
        } else if ((PUTS_A_KEY_AND_A_VALUE.contains(name) || name.equals("replace"))
                && args.size() >= 2) {
            out.addAll(putIn(KEY, args.get(0)));
            out.addAll(putIn(ELEMENT, args.get(1)));
        } else if (PUTS_ALL.contains(name) && !args.isEmpty()) {
            out.addAll(held(args.get(args.size() - 1)));
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

    /** What putting this value in one slot of a container leaves on the container. */
    private static Set<Tag> putIn(String slot, Val value) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : value.tags()) {
            if (each.kind() == Kind.COLLECTION) {
                out.add(Tag.held(each.origin(), slot));
            } else if (each.isHeld()) {
                out.add(Tag.held(each.origin(), slot + each.site()));
            }
        }
        return out;
    }

    /**
     * What is taken out of one slot: the copy itself where nothing is left of the path, and what
     * the copy's own slots hold where something is.
     */
    private static Set<Tag> takenOut(Set<Tag> held, String slot) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            if (each.site().startsWith(slot)) {
                String rest = each.site().substring(slot.length());
                out.add(rest.isEmpty() ? new Tag(Kind.COLLECTION, each.origin())
                        : Tag.held(each.origin(), rest));
            }
        }
        return out;
    }

    /** What a view of the elements of a slot holds: the same, as elements of the view. */
    private static Set<Tag> takenAlong(Set<Tag> held, String slot) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            if (each.site().startsWith(slot)) {
                out.add(each);
            }
        }
        return out;
    }

    /** What the keys of a map are, as the elements of a set. */
    private static Set<Tag> rekeyed(Set<Tag> held) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            if (each.site().startsWith(KEY)) {
                out.add(Tag.held(each.origin(), ELEMENT + each.site().substring(KEY.length())));
            }
        }
        return out;
    }

    /** What a set of the entries of a map holds: what the map holds, one slot further in. */
    private static Set<Tag> prefixed(Set<Tag> held, String slot) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : held) {
            out.add(Tag.held(each.origin(), slot + each.site()));
        }
        return out;
    }
}
