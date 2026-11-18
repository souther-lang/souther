package souther.compiler.partition;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.lang.reflect.Method;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Stream;

/**
 * The state of one reader that a reading kept to be taken again depends on and must leave alone.
 *
 * <p>Each piece of that state is a part made here and held by the reader as a field. The part says
 * once, where the field is declared, how a reading kept is compared on it when it is taken again
 * ({@link Compared}), whether a reading must leave it as it found it, and whether it is compared
 * only for a reading that asked after it. A part is entered for the extent of a reading through
 * the part, which puts it back however the reading ends ({@link Restore}), and a reading that asks
 * after it does so through the part, which records the asking. A field of the reader that is no
 * part says why ({@link NoPartOfAReading}).
 */
final class ReadingState {

    /** A piece of state that says what has been added to it, as a value that is the same only
     *  while nothing has. */
    interface Marked {
        Object mark();
    }

    /**
     * What a field of a reader that is no part of this is, which is why a reading kept is neither
     * compared on it nor made to leave it alone. Read by a test of the reader's fields, and by
     * nothing that keeps or takes a reading.
     */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.FIELD)
    @interface NoPartOfAReading {
        Why value();

        enum Why {
            /** The same at every reading of one reader. */
            FIXED,
            /** The parts met, in order, which the readings kept carry and meet again. */
            LEDGER,
            /** The readings left, which a reading is charged and a reading taken again is not. */
            BUDGET,
            /** Only added to, and never asked after by a reading: what a reading added is still
             *  there when it is taken again. */
            ACCRUES,
            /** Answers worked out once whatever asked, and so the same however first asked. */
            CACHE,
            /** The readings kept. */
            MEMO,
            /** A count that tells a reading what it did. */
            COUNTER,
            /** This state itself. */
            STATE
        }
    }

    /** How a reading kept is compared on a part where it is taken again. */
    enum Compared {
        /** By what it holds, compared with {@link Object#equals}: a collection is copied, so a
         *  later change to it is not a change to what was taken. */
        BY_VALUE,
        /** As the very object: what the reader looks up by identity is the same only for the same
         *  object. */
        BY_IDENTITY,
        /** Only whether there is one. */
        BY_PRESENCE,
        /** By what it says it has been told ({@link Marked#mark}): an object that is changed in
         *  place is the same only while it has been told nothing more. */
        BY_MARK,
        /** Not at all. */
        NOT
    }

    /** What a part entered for an extent is put back to when the extent ends. */
    interface Restore extends AutoCloseable {
        @Override
        void close();
    }

    /**
     * The inputs of a reading as they stood.
     *
     * @param values   what the inputs were, as each is compared ({@link Compared})
     * @param asked    what the aggregates being read were
     * @param contents what each input whose contents a reading may ask after held, by the place of
     *                 the input among {@code values}, and null for each other: a reading that
     *                 asked what one holds depends on that and not on its being there
     */
    record Inputs(List<Object> values, Object asked, List<Object> contents) {}

    private final List<Part> inputs = new ArrayList<>();
    private final List<Part> guards = new ArrayList<>();
    private final List<Part> searches = new ArrayList<>();
    private Layers<?> aggregates;
    /** The next bit a part a reading may leave unasked is told by. */
    private int nextBit = 1;
    /** Which of the parts a reading may leave unasked the reading being made has asked after. */
    private int consulted;

    /**
     * A piece of the state. Entered and asked after through itself, so what it is to a reading kept
     * is said where it is made.
     */
    abstract static sealed class Part permits Scoped, Members, Bindings, Layers {

        final ReadingState state;
        final Compared compared;
        /** The bit asking after this is told by, or 0 where it is compared for every reading. */
        int askedBit;
        /** The bit asking what this holds is told by, or 0 where what it holds is not compared. */
        int contentBit;

        Part(ReadingState state, Compared compared) {
            this.state = state;
            this.compared = compared;
        }

        /** What this holds, unasked: for comparing it and for putting it back. */
        abstract Object held();

        /** What a reading that must leave this alone is compared on. */
        Object guarded() {
            return held();
        }

        final void asked() {
            state.consulted |= askedBit;
        }

        final void askedWhatItHolds() {
            state.consulted |= askedBit | contentBit;
        }
    }

    /**
     * A value set for the extent of a reading and put back after it.
     *
     * @param <T> what it holds; null where nothing is set
     */
    static final class Scoped<T> extends Part {

        private T value;

        private Scoped(ReadingState state, Compared compared, T value) {
            super(state, compared);
            this.value = value;
        }

        /** What is set, which a reading that reads it asks after. */
        T get() {
            asked();
            return value;
        }

        /** What is set, where the reading reads what it holds and not only that there is one. */
        T contents() {
            askedWhatItHolds();
            return value;
        }

        /** Sets {@code value} until what is returned is closed, which puts back what was set. */
        Restore set(T value) {
            T before = this.value;
            this.value = value;
            return () -> this.value = before;
        }

        /** What {@code reading} comes to with {@code value} set for it. */
        <R> R during(T value, Supplier<R> reading) {
            try (Restore _ = set(value)) {
                return reading.get();
            }
        }

        /** Sets what this begins as, for a reader just made. */
        void beginAs(T value) {
            this.value = value;
        }

        @Override
        Object held() {
            return value;
        }
    }

    /** Members, each in for the extent of a reading. */
    static final class Members<E> extends Part {

        private final Set<E> held;

        private Members(ReadingState state, Compared compared, Set<E> held) {
            super(state, compared);
            this.held = held;
        }

        boolean contains(Object member) {
            return held.contains(member);
        }

        boolean isEmpty() {
            return held.isEmpty();
        }

        Stream<E> stream() {
            return held.stream();
        }

        /**
         * Puts {@code member} in until what is returned is closed, which takes it out. It is not
         * in: a member already in is no member entered here, and taking it out would take out the
         * one around.
         */
        Restore adding(E member) {
            if (!held.add(member)) {
                throw new IllegalStateException(member + " is already in");
            }
            return () -> held.remove(member);
        }

        /** Holds none until what is returned is closed, which puts back what was held. */
        Restore emptied() {
            List<E> before = List.copyOf(held);
            held.clear();
            return () -> {
                held.clear();
                held.addAll(before);
            };
        }

        @Override
        Object held() {
            return held;
        }
    }

    /** Keys each bound to a value for the extent of a reading. */
    static final class Bindings<K, V> extends Part {

        private final Map<K, V> held;

        private Bindings(ReadingState state, Compared compared, Map<K, V> held) {
            super(state, compared);
            this.held = held;
        }

        V get(Object key) {
            return held.get(key);
        }

        boolean containsKey(Object key) {
            return held.containsKey(key);
        }

        int size() {
            return held.size();
        }

        boolean isEmpty() {
            return held.isEmpty();
        }

        Set<Map.Entry<K, V>> entrySet() {
            return Collections.unmodifiableMap(held).entrySet();
        }

        /**
         * Binds {@code key} to {@code value} until what is returned is closed, which puts back what
         * the key was bound to before, or leaves it unbound where it was not.
         */
        Restore binding(K key, V value) {
            boolean had = held.containsKey(key);
            V before = held.put(key, value);
            return () -> {
                if (had) {
                    held.put(key, before);
                } else {
                    held.remove(key);
                }
            };
        }

        /** {@link #binding} of each of {@code keys}, all put back together. */
        Restore bindingEach(Collection<? extends K> keys, V value) {
            List<Restore> each = new ArrayList<>(keys.size());
            for (K key : keys) {
                each.add(binding(key, value));
            }
            return () -> {
                for (Restore one : each.reversed()) {
                    one.close();
                }
            };
        }

        /** Binds {@code key} to {@code value} for good where it is not bound: the first binding
         *  of a key is the one it keeps. */
        void keepFirst(K key, V value) {
            held.putIfAbsent(key, value);
        }

        @Override
        Object held() {
            return held;
        }
    }

    /** Values each on top for the extent of a reading, the newest on top. */
    static final class Layers<E> extends Part {

        private final List<E> held = new ArrayList<>();
        private final boolean guardsTheNewest;

        private Layers(ReadingState state, Compared compared, boolean guardsTheNewest) {
            super(state, compared);
            this.guardsTheNewest = guardsTheNewest;
        }

        /** The one on top, or null where there is none. */
        E newest() {
            return held.isEmpty() ? null : held.getLast();
        }

        boolean isEmpty() {
            return held.isEmpty();
        }

        List<E> oldestFirst() {
            return Collections.unmodifiableList(held);
        }

        List<E> newestFirst() {
            return Collections.unmodifiableList(held).reversed();
        }

        /** Puts {@code value} on top until what is returned is closed, which takes it off. */
        Restore pushing(E value) {
            held.add(value);
            return () -> {
                if (held.isEmpty() || held.getLast() != value) {
                    throw new IllegalStateException(value + " is not on top to be taken off");
                }
                held.removeLast();
            };
        }

        @Override
        Object held() {
            return held;
        }

        @Override
        Object guarded() {
            return guardsTheNewest ? newest() : held;
        }
    }

    private <P extends Part> P input(P part) {
        inputs.add(part);
        return part;
    }

    private <P extends Part> P guarded(P part) {
        guards.add(part);
        return part;
    }

    private void askedFor(Part part) {
        part.askedBit = nextBit;
        nextBit <<= 1;
    }

    /** A value a reading is compared on as {@code compared} says, null until it is set. */
    <T> Scoped<T> setting(Compared compared) {
        return setting(compared, null);
    }

    /** The same, {@code initial} until it is set. */
    <T> Scoped<T> setting(Compared compared, T initial) {
        return input(new Scoped<>(this, compared, initial));
    }

    /** The same, compared only for a reading that asked after it ({@link Scoped#get}): what a
     *  reading never asked after is no part of what it comes to. */
    <T> Scoped<T> askedAfter(Compared compared) {
        Scoped<T> out = setting(compared);
        askedFor(out);
        return out;
    }

    /** A value a reading is compared on and must leave as it found it, by what it holds. */
    <T> Scoped<T> guarded() {
        return guarded(setting(Compared.BY_VALUE));
    }

    /** The same, of an object changed in place that says what it has been told: compared on that
     *  ({@link Compared#BY_MARK}). */
    <T extends Marked> Scoped<T> guardedByItsMark() {
        return guarded(setting(Compared.BY_MARK));
    }

    /**
     * A place a reading adds to where there is one: compared by whether there is one, and left as
     * found.
     */
    <T> Scoped<T> writtenInto() {
        return guarded(setting(Compared.BY_PRESENCE));
    }

    /**
     * The same, compared only for a reading that asked after it, and by what it holds where the
     * reading asked that ({@link Scoped#contents}).
     */
    <T> Scoped<T> writtenIntoAndAskedAfter() {
        Scoped<T> out = writtenInto();
        askedFor(out);
        out.contentBit = nextBit;
        nextBit <<= 1;
        return out;
    }

    /** A value set for the extent of a reading that a reading kept is not compared on. */
    <T> Scoped<T> notCompared(T value) {
        return new Scoped<>(this, Compared.NOT, value);
    }

    /** Members a reading is compared on by which they are. */
    <E> Members<E> members() {
        return input(new Members<>(this, Compared.BY_VALUE, new HashSet<>()));
    }

    /** Bindings a reading is compared on by what they bind. */
    <K, V> Bindings<K, V> bindings() {
        return input(new Bindings<>(this, Compared.BY_VALUE, new HashMap<>()));
    }

    /** A stack a reading is compared on by what is on it. */
    <E> Layers<E> stack() {
        return input(new Layers<>(this, Compared.BY_VALUE, false));
    }

    /**
     * The candidates being tried, newest on top: a reading must not have said anything into the one
     * on top, nor be read under another.
     */
    <E> Layers<E> trials() {
        return guarded(new Layers<>(this, Compared.NOT, true));
    }

    /**
     * The aggregates of the way being read, compared for a reading that asked after them, each as
     * the very aggregate.
     */
    <E> Layers<E> aggregates() {
        Layers<E> out = new Layers<>(this, Compared.NOT, false);
        aggregates = out;
        return out;
    }

    /**
     * Members of a search whose body is being read, which the reading adds to what the search
     * reaches: a reading taken would not add it, and a reading made would leave it half of what it
     * is, so a search in progress is no place to keep or to take one.
     */
    <E> Members<E> searchMembers() {
        Members<E> out = new Members<>(this, Compared.NOT, new HashSet<>());
        searches.add(out);
        return out;
    }

    /** Bindings of such a search, held by the identity of each key. */
    <K, V> Bindings<K, V> searchBindings() {
        Bindings<K, V> out = new Bindings<>(this, Compared.NOT, new IdentityHashMap<>());
        searches.add(out);
        return out;
    }

    /** Whether no search is in progress, which is where a reading may be kept or taken. */
    boolean holdsNothing() {
        for (Part each : searches) {
            boolean empty = switch (each.held()) {
                case Collection<?> collection -> collection.isEmpty();
                case Map<?, ?> map -> map.isEmpty();
                default -> throw new IllegalStateException("a search holds a collection");
            };
            if (!empty) {
                return false;
            }
        }
        return true;
    }

    /** The inputs as they stand. */
    Inputs inputs() {
        List<Object> values = new ArrayList<>(inputs.size());
        List<Object> contents = new ArrayList<>(inputs.size());
        for (Part each : inputs) {
            Object value = each.held();
            contents.add(each.contentBit != 0 && value != null ? snapshotOf(heldIn(value)) : null);
            values.add(switch (each.compared) {
                case BY_PRESENCE -> Boolean.valueOf(value != null);
                case BY_IDENTITY -> new Same(value);
                case BY_VALUE -> copyOf(value);
                case BY_MARK -> value == null ? null : ((Marked) value).mark();
                case NOT -> throw new IllegalStateException("an input is compared");
            });
        }
        return new Inputs(Collections.unmodifiableList(values),
                aggregates == null ? null : snapshotOf(aggregates.held()),
                Collections.unmodifiableList(contents));
    }

    /**
     * A number that is the same for inputs either comparison calls the same, whatever was asked
     * after: the values are what every comparison asks, and nothing a reading's having asked after
     * something or not decides is taken into it.
     */
    int requiredInputsHash(Inputs inputs) {
        return inputs.values().hashCode();
    }

    /**
     * Whether {@code now} are the inputs {@code then} were, every one of them, and what each holds
     * where the reading {@code then} was of asked what it holds; those of the aggregates only where
     * {@code askedMatters}.
     */
    boolean sameInputs(Inputs then, Inputs now, boolean askedMatters, int consulted) {
        return same(then, now, consulted, false, null)
                && (!askedMatters || Objects.equals(then.asked(), now.asked()));
    }

    /**
     * The same, but for the inputs a reading may leave unasked that the reading {@code then} was of
     * never asked after, and for {@code aside}: what an input that was not asked after stood as is
     * no part of what the reading came to. The aggregates are not compared.
     */
    boolean sameAskedInputsBut(Inputs then, Inputs now, int consulted, Part aside) {
        return same(then, now, consulted, true, aside);
    }

    private boolean same(Inputs then, Inputs now, int consulted, boolean onlyWhereAsked,
                         Part aside) {
        for (int at = 0; at < inputs.size(); at++) {
            Part each = inputs.get(at);
            if (each == aside
                    || (onlyWhereAsked && each.askedBit != 0
                            && (consulted & each.askedBit) == 0)) {
                continue;
            }
            if (!Objects.equals(then.values().get(at), now.values().get(at))) {
                return false;
            }
            if ((consulted & each.contentBit) != 0
                    && !Objects.equals(then.contents().get(at), now.contents().get(at))) {
                return false;
            }
        }
        return true;
    }

    /** Begins a reading that asks after nothing yet, and returns what the one around had asked. */
    int startConsulting() {
        int before = consulted;
        consulted = 0;
        return before;
    }

    /** Ends the reading begun at {@code before}, which the one around has asked after as well,
     *  and returns what it asked after. */
    int endConsulting(int before) {
        int mine = consulted;
        consulted = before | mine;
        return mine;
    }

    /** What a reading taken again asked after, asked after by the reading it is taken in. */
    void consultAgain(int consulted) {
        this.consulted |= consulted;
    }

    /** {@code consulted} with {@code part} not asked after. */
    static int without(int consulted, Part part) {
        return consulted & ~part.askedBit;
    }

    /** What the state a reading must leave alone is, to be compared with it afterwards: the very
     *  object it is and everything that can be reached through it. */
    List<Object[]> guards() {
        List<Object[]> out = new ArrayList<>(guards.size());
        for (Part each : guards) {
            Object held = each.guarded();
            out.add(new Object[] {held, snapshotOf(held)});
        }
        return out;
    }

    /** Whether the state a reading must leave alone is as {@code then} found it. */
    boolean sameGuards(List<Object[]> then, List<Object[]> now) {
        return sameGuardsBut(then, now, _ -> false);
    }

    /** The same, but for the guards that are one of {@code aside}, which the caller answers for. */
    boolean sameGuardsBut(List<Object[]> then, List<Object[]> now, Predicate<Object> aside) {
        for (int at = 0; at < then.size(); at++) {
            Object[] before = then.get(at);
            Object[] after = now.get(at);
            if (aside.test(before[0]) && aside.test(after[0])) {
                continue;
            }
            if (before[0] != after[0] || !Objects.equals(before[1], after[1])) {
                return false;
            }
        }
        return true;
    }

    /**
     * What {@code value} is and holds, to be compared with what it is and holds later: what an
     * object that says what it has been told says ({@link Marked#mark}), and otherwise the lists
     * and maps of lists a ledger or the aggregates hold, down to each object in them as the very
     * one. An object added to a list held under a key is a change.
     */
    static Object snapshotOf(Object value) {
        return switch (value) {
            case null -> null;
            case Marked marked -> marked.mark();
            case Map<?, ?> map -> {
                Map<Object, Object> held = new HashMap<>();
                for (Map.Entry<?, ?> each : map.entrySet()) {
                    held.put(new Same(each.getKey()), snapshotOf(each.getValue()));
                }
                yield held;
            }
            case Collection<?> collection -> {
                List<Object> held = new ArrayList<>(collection.size());
                for (Object each : collection) {
                    held.add(new Same(each));
                }
                yield held;
            }
            default -> new Same(value);
        };
    }

    /**
     * Whether the objects the state holds are looked into for a collection that can change inside
     * them.
     *
     * <p>What is compared by what it holds, or as the very object, is the same while it is not
     * changed in place; a collection in a record that is added to is a change that comparison
     * never sees. A test turns this on and reads a population of models: a record that holds a
     * collection which is not immutable fails where the state is taken.
     */
    static volatile boolean auditing = false;

    /** What the audit found: the record and component of each collection that can change. */
    static final Set<String> FOUND = ConcurrentHashMap.newKeySet();

    /** The collections the state holds that can change, in {@code held} and the records in it. */
    private static void audit(Object held, Set<Object> seen) {
        if (held == null || !held.getClass().isRecord() || !seen.add(held)) {
            return;
        }
        for (RecordComponent each : held.getClass().getRecordComponents()) {
            Object value;
            try {
                Method accessor = each.getAccessor();
                accessor.setAccessible(true);
                value = accessor.invoke(held);
            } catch (ReflectiveOperationException e) {
                throw new IllegalStateException(each.getName(), e);
            }
            if ((value instanceof Collection<?> || value instanceof Map<?, ?>)
                    && !immutable(value)) {
                FOUND.add(held.getClass().getName() + "." + each.getName() + " is a "
                        + value.getClass().getName());
            }
            audit(value, seen);
        }
    }

    private static boolean immutable(Object collection) {
        String name = collection.getClass().getName();
        return name.startsWith("java.util.ImmutableCollections$")
                || name.startsWith("java.util.Collections$Empty")
                || name.startsWith("java.util.Collections$Singleton");
    }

    /** An object that is the same only as itself, whatever it is equal to. */
    private record Same(Object of) {

        Same {
            if (auditing) {
                audit(of, Collections.newSetFromMap(new IdentityHashMap<>()));
            }
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Same that && that.of == of;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(of);
        }
    }

    /**
     * What {@code value} holds, as a collection: a ledger's entries, where it is a ledger. A
     * ledger's revision says which history it stands at and not what it holds, and an input
     * compared by what it holds is compared on that.
     */
    private static Object heldIn(Object value) {
        return value instanceof Ledger ledger ? ledger.contents() : value;
    }

    /** A copy of {@code value} that a later change to it does not reach, where it is something
     *  that is changed. */
    private static Object copyOf(Object held) {
        Object value = heldIn(held);
        if (auditing) {
            auditEach(value);
        }
        return switch (value) {
            case null -> null;
            case Set<?> set -> set.isEmpty() ? Set.of() : new HashSet<>(set);
            case Map<?, ?> map -> map.isEmpty() ? Map.of() : new HashMap<>(map);
            case Collection<?> collection ->
                    collection.isEmpty() ? List.of() : new ArrayList<>(collection);
            default -> value;
        };
    }

    /** {@link #audit} of {@code value} and of what is in it, where it is a collection or a map. */
    private static void auditEach(Object value) {
        Set<Object> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        switch (value) {
            case Map<?, ?> map -> map.forEach((key, each) -> {
                audit(key, seen);
                audit(each, seen);
            });
            case Collection<?> collection -> collection.forEach(each -> audit(each, seen));
            case null -> { }
            default -> audit(value, seen);
        }
    }
}
