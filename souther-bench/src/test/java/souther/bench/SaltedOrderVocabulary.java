package souther.bench;

import souther.bench.SaltedOrder.Kind;
import souther.bench.SaltedOrder.Tag;
import souther.bench.SaltedOrder.Val;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.publish.CanonicalArrangement;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.query.WeakeningSet;

import java.lang.invoke.MethodType;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What each call of the Java library does with an order, and which calls of this compiler's own put
 * one.
 *
 * <p><b>The crossings are found, not typed.</b> A method that puts an unordered value in an order
 * is named here by the class that declares it, so that one renamed or moved stops this compiling
 * and is not a string that matches nothing. The identity is owner, name and descriptor: a method
 * that happens to be called {@code keep} on some other class is not one, and neither is the same
 * name taking something else.
 *
 * <p>What the library calls are is a table of what each does with the order of what it is given.
 * A call this table does not know, handed something that came out of a copy, is not assumed to be
 * harmless — {@link Outcome#unmodeled} — so that a reader using a call nobody classified is refused
 * rather than passed.
 *
 * <p><b>A sort is a crossing exactly as far as its comparator leaves no two things tied.</b> What
 * the comparator is is not read here: a reader that sorts by a key two elements can share puts them
 * in the order the run gave, and this passes it.
 */
final class SaltedOrderVocabulary {

    private SaltedOrderVocabulary() {}

    /** A method as a class file names it. */
    record Signature(String owner, String name, String descriptor) {

        static Signature of(Method method) {
            return new Signature(method.getDeclaringClass().getName().replace('.', '/'),
                    method.getName(), MethodType.methodType(method.getReturnType(),
                            method.getParameterTypes()).toMethodDescriptorString());
        }

        String spelled() {
            return owner.replace('/', '.') + "." + name;
        }
    }

    /** What a call does to what it is handed. */
    record Outcome(Val result, List<Push> pushes, List<Val> clears, List<Feed> feeds,
                   List<String> crossedBy, boolean unmodeled, String endsAs) {

        Outcome(Val result, List<Push> pushes, List<Val> clears, List<Feed> feeds,
                List<String> crossedBy, boolean unmodeled) {
            this(result, pushes, clears, feeds, crossedBy, unmodeled, "");
        }

        static Outcome returning(Val result) {
            return new Outcome(result, List.of(), List.of(), List.of(), List.of(), false);
        }

        static Outcome refused() {
            return new Outcome(Val.CLEAN, List.of(), List.of(), List.of(), List.of(), true);
        }

        /** A call that reads what it is given and answers nothing with it, said in words. */
        static Outcome ending(String how) {
            return new Outcome(Val.CLEAN, List.of(), List.of(), List.of(), List.of(), false, how);
        }

        Outcome endingAs(String how) {
            return new Outcome(result, pushes, clears, feeds, crossedBy, unmodeled, how);
        }

        Outcome feeding(List<Feed> more, boolean returns) {
            List<Feed> all = new ArrayList<>(feeds);
            for (Feed each : more) {
                all.add(new Feed(each.functions(), each.elements(), returns));
            }
            return new Outcome(result, pushes, clears, all, crossedBy, unmodeled, endsAs);
        }
    }

    /** Tags added to every place an object is held. */
    record Push(Val into, Set<Tag> tags) {}

    /**
     * Elements handed to the functions a call was given.
     *
     * @param functions the functions
     * @param elements  what each argument after the ones they captured is
     * @param returns   whether what they return is part of what the call returns
     */
    record Feed(Set<Tag> functions, List<Set<Tag>> elements, boolean returns) {}

    /** One call: what it was made on, with what, and what it says it returns. */
    record Call(String owner, String name, String descriptor, Val receiver, List<Val> args,
                boolean isStatic, boolean returnsAValue, boolean returnsAReference,
                boolean asksForExactlyOne) {

        /**
         * What taking one of a plurality by where it stands makes of it: the first of many is the
         * order's to say, and the first of one is the one there is.
         */
        Kind whatSelectingOneMakes() {
            return asksForExactlyOne ? Kind.PICKED : Kind.CHOSEN;
        }

        List<Val> everything() {
            List<Val> out = new ArrayList<>(args);
            out.add(receiver);
            return out;
        }

        /** What in this call came out of a copy. */
        Set<Tag> tainted() {
            Set<Tag> out = new LinkedHashSet<>();
            for (Val each : everything()) {
                for (Tag tag : each.tags()) {
                    if (tag.cameOutOfACopy()) {
                        out.add(tag);
                    }
                }
            }
            return out;
        }
    }

    private static final Set<Signature> CROSSINGS = crossings();

    private static final Set<Signature> FOLDS = folds();

    private static Set<Signature> crossings() {
        Set<Signature> out = new LinkedHashSet<>();
        out.add(Signature.of(method(CanonicalSelection.Order.class, "keep", Collection.class)));
        out.add(Signature.of(method(CanonicalArrangement.Order.class, "arrange",
                Collection.class)));
        out.add(Signature.of(method(NumericTerms.class, "inOrder", Collection.class)));
        out.add(Signature.of(method(NumericTerms.class, "entriesInOrder", Map.class)));
        return out;
    }

    /**
     * Operations that take a plurality and do not care which comes first, by their own contract.
     *
     * <p>A set of weakenings is one whose union is idempotent, commutative and associative, and
     * says so where it is declared. What is handed to one of its makers is folded, and an order it
     * was walked in is not in what comes out.
     */
    private static Set<Signature> folds() {
        Set<Signature> out = new LinkedHashSet<>();
        out.add(Signature.of(method(WeakeningSet.class, "ofAll", Collection.class)));
        return out;
    }

    private static Method method(Class<?> owner, String name, Class<?>... parameters) {
        try {
            return owner.getMethod(name, parameters);
        } catch (NoSuchMethodException gone) {
            throw new AssertionError(owner.getName() + "." + name + " is named here as a crossing"
                    + " and is not there", gone);
        }
    }

    /** Whether a call of this compiler's own puts what it is given in an order. */
    static boolean crosses(Signature call) {
        return CROSSINGS.contains(call);
    }

    /** Whether a call of this compiler's own folds what it is given without regard to order. */
    static boolean folds(Signature call) {
        return FOLDS.contains(call);
    }

    private static final Set<String> IN_ORDER = Set.of(
            "java/util/ArrayList", "java/util/LinkedList", "java/util/ArrayDeque",
            "java/util/Vector", "java/util/Stack", "java/util/LinkedHashSet",
            "java/util/LinkedHashMap", "java/lang/StringBuilder", "java/lang/StringBuffer",
            "java/util/concurrent/CopyOnWriteArrayList", "java/util/PriorityQueue", "array");

    private static final Set<String> IN_ORDER_BY_INTERFACE = Set.of(
            "java/util/List", "java/util/Deque", "java/util/Queue", "java/util/Collection",
            "java/util/SequencedCollection", "java/util/SequencedSet", "java/util/SequencedMap",
            "java/lang/Appendable", "java/lang/CharSequence");

    private static final Set<String> WITHOUT_ORDER = Set.of(
            "java/util/HashSet", "java/util/HashMap", "java/util/IdentityHashMap",
            "java/util/WeakHashMap", "java/util/concurrent/ConcurrentHashMap");

    private static final Set<String> BY_ITS_OWN_ORDER = Set.of(
            "java/util/TreeSet", "java/util/TreeMap", "java/util/EnumSet", "java/util/EnumMap",
            "java/util/concurrent/ConcurrentSkipListMap",
            "java/util/concurrent/ConcurrentSkipListSet");

    private static boolean putsInItsOwnOrder(String made) {
        return made != null && BY_ITS_OWN_ORDER.contains(made);
    }

    private static final Set<String> STARTS_A_TRAVERSAL = Set.of(
            "iterator", "listIterator", "spliterator", "stream", "parallelStream");

    private static final Set<String> IS_A_VIEW = Set.of(
            "keySet", "values", "entrySet", "sequencedKeySet", "sequencedValues",
            "sequencedEntrySet", "subList", "headSet", "tailSet", "subSet", "headMap", "tailMap",
            "subMap", "descendingSet", "descendingMap", "reversed");

    private static final Set<String> KEEPS_TRAVERSING = Set.of(
            "boxed", "sequential", "parallel", "unordered", "onClose", "distinct", "asLongStream",
            "asDoubleStream", "mapToObj", "mapToInt", "mapToLong", "mapToDouble", "map",
            "flatMap", "flatMapToInt", "filter", "peek", "mapMulti");

    private static final Set<String> CUTS_BY_POSITION = Set.of(
            "limit", "skip", "takeWhile", "dropWhile");

    private static final Set<String> STEPS = Set.of("next", "nextElement", "previous");

    private static final Set<String> SELECTS_ONE = Set.of(
            "findFirst", "findAny", "getFirst", "getLast", "first", "last", "firstKey", "lastKey",
            "firstEntry", "lastEntry", "pollFirst", "pollLast", "pollFirstEntry", "pollLastEntry",
            "removeFirst", "removeLast", "peekFirst", "peekLast", "element", "elementAt", "min",
            "max", "reduce", "pop", "poll", "peek", "lower", "higher", "floor", "ceiling",
            "lowerKey", "higherKey", "floorKey", "ceilingKey", "lowerEntry", "higherEntry",
            "floorEntry", "ceilingEntry");

    private static final Set<String> PASSES_THROUGH = Set.of(
            "unmodifiableSet", "unmodifiableMap", "unmodifiableCollection", "unmodifiableList",
            "unmodifiableSequencedSet", "unmodifiableSequencedMap",
            "unmodifiableSequencedCollection", "unmodifiableSortedSet", "unmodifiableSortedMap",
            "requireNonNull", "requireNonNullElse", "requireNonNullElseGet", "ofNullable",
            "orElse", "orElseGet", "orElseThrow", "or", "getKey", "getValue", "entry", "getAsInt",
            "getAsLong", "getAsDouble", "cast");

    private static final Set<String> ASKS_ONLY = Set.of(
            "contains", "containsAll", "containsKey", "containsValue", "isEmpty", "size", "equals",
            "hashCode", "count", "sum", "average", "anyMatch", "allMatch", "noneMatch",
            "getOrDefault", "isPresent", "hasNext", "hasMoreElements", "hasPrevious", "compare",
            "compareTo", "nextIndex", "previousIndex", "getClass", "isInstance", "length",
            "charAt");

    /**
     * Calls that hand a function what one key or one payload holds, and walk nothing: what the
     * function is given is asked for by name, so it is not the element a walk is at.
     */
    private static final Set<String> ASKS_BY_KEY = Set.of(
            "merge", "compute", "computeIfAbsent", "computeIfPresent", "ifPresent",
            "ifPresentOrElse", "orElseGet", "getOrDefault");

    private static final Set<String> VISITS = Set.of(
            "forEach", "forEachOrdered", "forEachRemaining", "ifPresent", "ifPresentOrElse",
            "removeIf", "replaceAll", "anyMatch", "allMatch", "noneMatch", "computeIfAbsent",
            "computeIfPresent", "compute", "merge");

    private static final Set<String> PUTS_ONE_IN = Set.of(
            "add", "put", "putIfAbsent", "addFirst", "addLast", "push", "offer", "offerFirst",
            "offerLast", "set", "replace", "append", "insert");

    private static final Set<String> PUTS_MANY_IN = Set.of("addAll", "putAll");

    private static final Set<String> MAKES_TEXT = Set.of(
            "toString", "join", "valueOf", "format", "formatted", "concat", "repeat", "strip",
            "trim", "substring", "toUpperCase", "toLowerCase", "replace", "replaceAll",
            "copyValueOf", "name", "deepToString", "hash", "requireNonNull", "toIdentityString");

    /** What a call does, given what it is handed. */
    static Outcome of(Call call) {
        Set<Tag> came = call.tainted();
        String name = call.name();
        if (name.equals("<init>")) {
            return constructed(call, came);
        }
        if (name.equals("sorted") || name.equals("sort")) {
            return sorted(call, came);
        }
        if (name.equals("collect")) {
            return collected(call);
        }
        if (call.owner().equals("java/util/stream/Collectors")) {
            return collector(call);
        }
        if (call.owner().equals("java/util/EnumSet") || call.owner().equals("java/util/EnumMap")) {
            return new Outcome(Val.CLEAN.withMade(call.owner()), List.of(), List.of(), List.of(),
                    came.isEmpty() ? List.of() : List.of(call.owner().replace('/', '.')), false);
        }
        if (came.isEmpty()) {
            return Outcome.returning(Val.CLEAN);
        }
        return over(call, came);
    }

    private static Outcome constructed(Call call, Set<Tag> came) {
        Val made = call.receiver();
        String type = call.owner();
        if (came.isEmpty()) {
            return Outcome.returning(Val.CLEAN);
        }
        if (IN_ORDER.contains(type)) {
            return pushing(made, orderedFrom(call.args(), true));
        }
        if (WITHOUT_ORDER.contains(type)) {
            return pushing(made, unorderedFrom(call.args()));
        }
        if (putsInItsOwnOrder(type)) {
            return new Outcome(Val.CLEAN, List.of(), List.of(), List.of(),
                    List.of(type.replace('/', '.')), false);
        }
        if (type.equals("java/util/AbstractMap$SimpleEntry")
                || type.equals("java/util/AbstractMap$SimpleImmutableEntry")) {
            return pushing(made, came);
        }
        if (isAnExceptionMessage(type)) {
            return Outcome.ending("the message of " + type.replace('/', '.'));
        }
        return Outcome.refused();
    }

    /**
     * Whether a class is one thrown, whose constructor takes a message.
     *
     * <p>The text an invariant violation is thrown with is read by whoever is looking at a defect,
     * and nothing a run answers is made of it. Where it names a set, that is the set in whatever
     * order it iterates, which is worth having read once and is not an answer.
     */
    private static boolean isAnExceptionMessage(String type) {
        return type.startsWith("java/") && (type.endsWith("Exception") || type.endsWith("Error"));
    }

    private static Outcome pushing(Val into, Set<Tag> tags) {
        return new Outcome(Val.CLEAN, tags.isEmpty() ? List.of() : List.of(new Push(into, tags)),
                List.of(), List.of(), List.of(), false);
    }

    /** What something made in an order holds once it is given these: the order they came in. */
    private static Set<Tag> orderedFrom(List<Val> given, boolean whole) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Val each : given) {
            for (Tag tag : each.tags()) {
                switch (tag.kind()) {
                    case COLLECTION, TRAVERSAL -> {
                        if (whole) {
                            out.add(new Tag(Kind.SEQUENCE, tag.origin()));
                        }
                    }
                    case SEQUENCE, CHOSEN -> out.add(tag.kind() == Kind.SEQUENCE ? tag
                            : new Tag(Kind.SEQUENCE, tag.origin(), tag.site()));
                    case PICKED -> out.add(new Tag(Kind.SEQUENCE, tag.origin()));
                    default -> { }
                }
            }
        }
        return out;
    }

    /**
     * What something made without an order holds once it is given these.
     *
     * <p>Every element a walk visits going in does not make the set an answer of the walk's order,
     * so a picked element is not carried; one selected by where it stood is.
     */
    private static Set<Tag> unorderedFrom(List<Val> given) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Val each : given) {
            for (Tag tag : each.tags()) {
                switch (tag.kind()) {
                    case COLLECTION, TRAVERSAL, SEQUENCE, PICKED ->
                            out.add(new Tag(Kind.COLLECTION, tag.origin()));
                    case CHOSEN -> {
                        out.add(new Tag(Kind.COLLECTION, tag.origin()));
                        out.add(tag);
                    }
                    default -> { }
                }
            }
        }
        return out;
    }

    private static Outcome sorted(Call call, Set<Tag> came) {
        List<Val> clears = new ArrayList<>();
        if (!call.returnsAValue()) {
            clears.add(call.receiver().isClean() && !call.args().isEmpty()
                    ? call.args().get(0) : call.receiver());
        }
        List<String> by = came.isEmpty() ? List.of()
                : List.of(call.owner().replace('/', '.') + "." + call.name());
        return new Outcome(Val.CLEAN, List.of(), clears, List.of(), by, false);
    }

    private static Outcome collector(Call call) {
        Set<Tag> tags = new LinkedHashSet<>();
        for (Val each : call.args()) {
            tags.addAll(each.functions());
        }
        Kind kind = switch (call.name()) {
            case "toList", "toUnmodifiableList", "joining", "toCollection" ->
                    Kind.ORDERED_COLLECTOR;
            default -> Kind.UNORDERED_COLLECTOR;
        };
        tags.add(new Tag(kind, call.name()));
        return Outcome.returning(Val.of(tags));
    }

    private static Outcome collected(Call call) {
        Val from = call.receiver();
        boolean ordered = false;
        Set<Tag> functions = new LinkedHashSet<>();
        for (Val each : call.args()) {
            ordered |= each.has(Kind.ORDERED_COLLECTOR);
            functions.addAll(each.functions());
        }
        if (!from.cameOutOfACopy()) {
            return Outcome.returning(Val.CLEAN);
        }
        Set<Tag> into = ordered ? from.as(Kind.SEQUENCE) : unorderedFrom(List.of(from));
        Outcome result = Outcome.returning(Val.of(into));
        if (functions.isEmpty()) {
            return result;
        }
        return result.feeding(List.of(new Feed(functions, List.of(from.as(Kind.PICKED)), false)),
                false);
    }

    /** A call on or with something that came out of a copy, of a kind nothing above settled. */
    private static Outcome over(Call call, Set<Tag> came) {
        String name = call.name();
        Val receiver = call.receiver();
        boolean library = inTheCollectionsLibrary(call.owner());
        Val walked = !library ? Val.CLEAN
                : receiver.collections().cameOutOfACopy() ? receiver.collections()
                : call.isStatic() ? collectionsIn(call.args()) : Val.CLEAN;
        Val everything = Val.of(came);
        List<Feed> feeds = feedsOf(call, walked.cameOutOfACopy() ? walked : everything);

        if (STARTS_A_TRAVERSAL.contains(name) && walked.cameOutOfACopy()) {
            return Outcome.returning(reconsidered(walked, Kind.TRAVERSAL));
        }
        if (IS_A_VIEW.contains(name) && walked.cameOutOfACopy()) {
            return Outcome.returning(Val.of(walked.tags()));
        }
        if (KEEPS_TRAVERSING.contains(name) && walked.cameOutOfACopy()) {
            return Outcome.returning(reconsidered(walked, Kind.TRAVERSAL)).feeding(feeds, true);
        }
        if (CUTS_BY_POSITION.contains(name) && walked.cameOutOfACopy()) {
            Set<Tag> chosen = new LinkedHashSet<>(walked.as(Kind.TRAVERSAL));
            chosen.addAll(walked.as(Kind.CHOSEN));
            return Outcome.returning(Val.of(chosen)).feeding(feeds, true);
        }
        if (name.equals("get") && call.descriptor().startsWith("(I)")
                && walked.cameOutOfACopy()) {
            return Outcome.returning(Val.of(walked.as(call.whatSelectingOneMakes())));
        }
        if (name.equals("get") && call.descriptor().startsWith("(Ljava/lang/Object;)")) {
            return Outcome.returning(Val.CLEAN).endingAs("asked what it holds");
        }
        if (name.equals("get") && call.descriptor().startsWith("()")) {
            return Outcome.returning(call.returnsAReference() ? everything : Val.CLEAN);
        }
        if (STEPS.contains(name) && walked.cameOutOfACopy()) {
            // The element a walk is at. A single step taken and no more is the first or the last,
            // and reads the same in the bytecode as the only one of a set of one — which is why it
            // is not told apart here from a step of a walk that goes on.
            return Outcome.returning(Val.of(walked.as(Kind.PICKED)));
        }
        if (name.equals("toString") && call.descriptor().startsWith("()")
                && walked.cameOutOfACopy()) {
            return Outcome.returning(Val.of(walked.as(Kind.SEQUENCE)));
        }
        if (SELECTS_ONE.contains(name) && walked.cameOutOfACopy()) {
            return Outcome.returning(Val.of(walked.as(call.whatSelectingOneMakes())))
                    .feeding(feeds, false);
        }
        if (name.equals("remove")) {
            return Outcome.returning(call.descriptor().startsWith("()") && walked.cameOutOfACopy()
                    ? Val.of(walked.as(call.whatSelectingOneMakes())) : Val.CLEAN);
        }
        if (ASKS_ONLY.contains(name) || VISITS.contains(name)) {
            return Outcome.returning(Val.CLEAN).feeding(feeds, false)
                    .endingAs(ASKS_ONLY.contains(name) ? "asked what it holds" : "visited");
        }
        if (PASSES_THROUGH.contains(name)
                || (name.equals("of") && call.owner().equals("java/util/Optional"))) {
            return Outcome.returning(call.returnsAReference() ? everything : Val.CLEAN);
        }
        if (library && materializesInOrder(call)) {
            return Outcome.returning(Val.of(orderedFrom(List.of(walkedOrArgs(call)), true)));
        }
        if (library && (name.equals("copyOf") || name.equals("of") || name.equals("ofEntries")
                || name.equals("toSet") || name.equals("toUnmodifiableSet"))) {
            return Outcome.returning(Val.of(unorderedFrom(call.everything())));
        }
        if (library && (PUTS_ONE_IN.contains(name) || PUTS_MANY_IN.contains(name))) {
            return filled(call, feeds);
        }
        if ((call.owner().startsWith("java/lang/") && MAKES_TEXT.contains(name))
                || call.owner().equals("java/util/Objects")) {
            return Outcome.returning(call.returnsAReference()
                    ? Val.of(textFrom(came)) : Val.CLEAN);
        }
        boolean onlyElements = true;
        for (Tag each : came) {
            onlyElements &= each.kind() == Kind.PICKED || each.kind() == Kind.CHOSEN;
        }
        if (onlyElements) {
            return Outcome.returning(call.returnsAReference() ? everything : Val.CLEAN);
        }
        return Outcome.refused();
    }

    /**
     * Whether a call is on something that holds a plurality, as against something that happens to
     * share a method name with one: {@code add} is a put into a list and is arithmetic on a number.
     */
    private static boolean inTheCollectionsLibrary(String owner) {
        return owner.startsWith("java/util/") && !owner.startsWith("java/util/function/")
                || owner.equals("java/lang/Iterable") || owner.equals("java/lang/StringBuilder")
                || owner.equals("java/lang/StringBuffer") || owner.equals("java/lang/Appendable")
                || owner.equals("java/lang/CharSequence");
    }

    private static boolean materializesInOrder(Call call) {
        String name = call.name();
        String owner = call.owner();
        return name.equals("toArray") || name.equals("toList") || name.equals("asList")
                || name.equals("toUnmodifiableList")
                || ((name.equals("copyOf") || name.equals("of")) && owner.equals("java/util/List"));
    }

    private static Val walkedOrArgs(Call call) {
        if (call.receiver().collections().cameOutOfACopy()) {
            return call.receiver().collections();
        }
        return collectionsIn(call.args());
    }

    private static Val collectionsIn(List<Val> values) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Val each : values) {
            out.addAll(each.collections().tags());
        }
        return Val.of(out);
    }

    /** The same values as another kind of walk: what was an element stays the one it was. */
    private static Val reconsidered(Val from, Kind kind) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag tag : from.tags()) {
            if (!tag.cameOutOfACopy()) {
                continue;
            }
            out.add(tag.isPositional() ? tag : new Tag(kind, tag.origin()));
        }
        return Val.of(out);
    }

    /** The functions in a call, each to be handed what a walk of what the call is on gives. */
    private static List<Feed> feedsOf(Call call, Val walked) {
        Set<Tag> functions = new LinkedHashSet<>();
        for (Val each : call.args()) {
            functions.addAll(each.functions());
        }
        if (functions.isEmpty() || !walked.cameOutOfACopy() || ASKS_BY_KEY.contains(call.name())) {
            return List.of();
        }
        boolean two = call.owner().equals("java/util/Map")
                && (call.name().equals("forEach") || call.name().equals("replaceAll"));
        List<Set<Tag>> elements = new ArrayList<>();
        for (int at = 0; at < (two ? 2 : 1); at++) {
            elements.add(walked.as(Kind.PICKED));
        }
        return List.of(new Feed(functions, elements, false));
    }

    /** What a text made of these says: the walk it was made along, or the element it was made of. */
    private static Set<Tag> textFrom(Set<Tag> came) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag tag : came) {
            out.add(tag.kind() == Kind.PICKED || tag.kind() == Kind.CHOSEN ? tag
                    : new Tag(Kind.SEQUENCE, tag.origin()));
        }
        return out;
    }

    /** A put into something, which keeps what it is given in an order or does not. */
    private static Outcome filled(Call call, List<Feed> feeds) {
        Val target = call.receiver();
        // Text put into a builder is the whole of what it says of what it is given, which for a
        // plurality is every element in the order it iterates.
        boolean many = PUTS_MANY_IN.contains(call.name())
                || call.name().equals("append") || call.name().equals("insert");
        boolean ownOrder = putsInItsOwnOrder(target.made());
        boolean keepsOrder = target.made() != null
                ? IN_ORDER.contains(target.made())
                : IN_ORDER_BY_INTERFACE.contains(call.owner());
        // What a map answers in the order of is its keys, and a value put beside a key is that key's
        // and takes no place of its own.
        boolean keyed = !many && call.args().size() == 2
                && (call.owner().endsWith("Map")
                        || (target.made() != null && target.made().endsWith("Map")));
        Set<Tag> into;
        if (ownOrder) {
            into = Set.of();
        } else if (keepsOrder) {
            into = orderedFrom(keyed ? call.args().subList(0, 1) : call.args(), many);
        } else {
            into = many ? unorderedFrom(call.args()) : elementsKept(call.args());
        }
        List<String> crossed = ownOrder && !call.tainted().isEmpty()
                ? List.of(target.made().replace('/', '.')) : List.of();
        Val result = call.name().equals("append") || call.name().equals("insert")
                ? target.plus(into) : Val.CLEAN;
        List<Push> pushes = into.isEmpty() ? List.of() : List.of(new Push(target, into));
        // A plurality put in whole as one element is held, and what is asked of it is asked of the
        // holder.
        String ends = !many && !call.args().isEmpty() && hasAPlurality(call.args())
                ? "held as one element of another" : "";
        return new Outcome(result, pushes, List.of(), feeds, crossed, false, ends);
    }

    private static boolean hasAPlurality(List<Val> values) {
        for (Val each : values) {
            if (each.collections().cameOutOfACopy()) {
                return true;
            }
        }
        return false;
    }

    /**
     * What one element put into something without an order leaves on it: the set is now made of
     * what a walk gave, and where the one was selected by position, of that too.
     */
    private static Set<Tag> elementsKept(List<Val> given) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Val each : given) {
            for (Tag tag : each.tags()) {
                if (tag.kind() == Kind.CHOSEN) {
                    out.add(tag);
                }
                if (tag.cameOutOfACopy() && tag.kind() != Kind.COLLECTION
                        && tag.kind() != Kind.TRAVERSAL && tag.kind() != Kind.SEQUENCE) {
                    out.add(new Tag(Kind.COLLECTION, tag.origin()));
                }
            }
        }
        return out;
    }
}
