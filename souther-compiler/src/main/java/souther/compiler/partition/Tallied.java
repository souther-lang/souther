package souther.compiler.partition;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * Values and collections that count every change made to them into one count they share
 * ({@link Changes}), for an object that says what it has been told by that count
 * ({@link ReadingState.Marked}).
 *
 * <p>The count moves because the thing changed and not because whoever changed it remembered to
 * move it: an object holding its state in these cannot change without its mark moving. What they
 * hand out cannot be changed through.
 *
 * <p>Whether something changed is read off what the collection answers, so the collections hold
 * no null: an answer of null is then only ever an absence. A part held inside another counts into
 * the same count, and one of another count is refused where it is put in, so a change inside it
 * moves the mark of whoever holds it. Everything put into a part, a key as much as a value, comes
 * through one admission ({@link Changes#admitted}), and an operation admits all it is handed
 * before it changes anything, so one that is refused leaves the part as it was.
 *
 * <p>What is admitted is the part handed in. An object that is no part and holds a part, or
 * holds anything else it changes in place, is held as the very object it is, and a change inside
 * it is not counted: what is put into a part is a value or a part, and nothing else.
 *
 * <p>An object made of these says so of every field it has ({@link InTheMark} for the few that
 * are set for an extent and are in the mark as they are), which a test asks of each.
 */
final class Tallied {

    private Tallied() {}

    /** A field that is no counted part and is in its owner's mark as the very value it is: set
     *  for an extent and put back, so that putting it back puts the mark back. */
    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.FIELD)
    @interface InTheMark {}

    /** A part, which counts every change made to it into {@link #changes}. */
    sealed interface Part permits Value, Group, Sequence, Table {
        Changes changes();
    }

    /** The count of changes shared by everything made from it. */
    static final class Changes {

        private long count;

        /** How many changes have been made to what was made from this. */
        long count() {
            return count;
        }

        private void moved() {
            count++;
        }

        /** {@code held}, which may be put inside a part of this count: anything but a part of
         *  another count. */
        private <T> T ownPart(T held) {
            if (held instanceof Part part && part.changes() != this) {
                throw new IllegalArgumentException(
                        "a part counted into another count, whose changes this would not see");
            }
            return held;
        }

        /** {@code held}, which may be put into a collection of this count as a key, a value or a
         *  member: something, and no part of another count. */
        private <T> T admitted(T held) {
            return ownPart(Objects.requireNonNull(held, "what is put in is something"));
        }

        /** Each of {@code held}, admitted before any of it is put in. */
        private <T> List<T> admittedEach(Collection<? extends T> held) {
            List<T> out = new ArrayList<>(held.size());
            for (T each : held) {
                out.add(admitted(each));
            }
            return out;
        }

        <T> Value<T> value(T initial) {
            return new Value<>(this, ownPart(initial));
        }

        /** A set, held in what {@code made} makes when the first member is put in. */
        <E> Group<E> group(Supplier<Set<E>> made) {
            return new Group<>(this, made);
        }

        <E> Sequence<E> sequence() {
            return new Sequence<>(this);
        }

        /** A table, held in what {@code made} makes when the first key is put in. */
        <K, V> Table<K, V> table(Supplier<Map<K, V>> made) {
            return new Table<>(this, made);
        }
    }

    /** A value, changed where another object is put in its place. Null where there is none: it
     *  is compared as the very object, which a null is as well as anything. */
    static final class Value<T> implements Part {
        private final Changes changes;
        private T held;

        private Value(Changes changes, T held) {
            this.changes = changes;
            this.held = held;
        }

        @Override
        public Changes changes() {
            return changes;
        }

        T get() {
            return held;
        }

        void set(T value) {
            changes.ownPart(value);
            if (value != held) {
                held = value;
                changes.moved();
            }
        }
    }

    /** Members, changed where one is put in or they are emptied. */
    static final class Group<E> implements Part {
        private final Changes changes;
        private final Supplier<Set<E>> made;
        private Set<E> held;

        private Group(Changes changes, Supplier<Set<E>> made) {
            this.changes = changes;
            this.made = made;
        }

        @Override
        public Changes changes() {
            return changes;
        }

        /** Puts {@code member} in, and answers whether it was not in already. */
        boolean add(E member) {
            changes.admitted(member);
            if (held == null) {
                held = made.get();
            }
            if (!held.add(member)) {
                return false;
            }
            changes.moved();
            return true;
        }

        /** Puts each of {@code members} in, all of them admitted first: one refused puts none
         *  in. */
        void addAll(Collection<? extends E> members) {
            for (E each : changes.admittedEach(members)) {
                add(each);
            }
        }

        boolean contains(Object member) {
            return held != null && held.contains(member);
        }

        boolean containsAll(Collection<?> members) {
            return held == null ? members.isEmpty() : held.containsAll(members);
        }

        boolean isEmpty() {
            return held == null || held.isEmpty();
        }

        void clear() {
            if (!isEmpty()) {
                held.clear();
                changes.moved();
            }
        }

        /** What it holds now, which changes as it does. */
        Set<E> view() {
            return held == null ? Set.of() : Collections.unmodifiableSet(held);
        }
    }

    /** Entries in the order they were added, changed where one is added. */
    static final class Sequence<E> implements Part {
        private final Changes changes;
        /** Made when the first entry is added. */
        private List<E> held;

        private Sequence(Changes changes) {
            this.changes = changes;
        }

        @Override
        public Changes changes() {
            return changes;
        }

        void add(E entry) {
            changes.admitted(entry);
            if (held == null) {
                held = new ArrayList<>();
            }
            held.add(entry);
            changes.moved();
        }

        int size() {
            return held == null ? 0 : held.size();
        }

        boolean isEmpty() {
            return held == null || held.isEmpty();
        }

        E getLast() {
            if (held == null) {
                throw new NoSuchElementException("nothing has been added");
            }
            return held.getLast();
        }

        /** What it holds now, which changes as it does. */
        List<E> view() {
            return held == null ? List.of() : Collections.unmodifiableList(held);
        }
    }

    /** Values under keys, changed where a key is put in or what is under one is replaced. */
    static final class Table<K, V> implements Part {
        private final Changes changes;
        private final Supplier<Map<K, V>> made;
        private Map<K, V> held;

        private Table(Changes changes, Supplier<Map<K, V>> made) {
            this.changes = changes;
            this.made = made;
        }

        @Override
        public Changes changes() {
            return changes;
        }

        private Map<K, V> held() {
            if (held == null) {
                held = made.get();
            }
            return held;
        }

        /** {@code key} and {@code value}, each admitted. */
        private void puttable(K key, V value) {
            changes.admitted(key);
            changes.admitted(value);
        }

        V get(Object key) {
            return held == null ? null : held.get(key);
        }

        V getOrDefault(Object key, V otherwise) {
            return held == null ? otherwise : held.getOrDefault(key, otherwise);
        }

        void put(K key, V value) {
            puttable(key, value);
            if (held().put(key, value) != value) {
                changes.moved();
            }
        }

        /** Puts {@code value} under {@code key} where nothing is, and answers whether it did. */
        boolean putIfAbsent(K key, V value) {
            puttable(key, value);
            if (held().putIfAbsent(key, value) != null) {
                return false;
            }
            changes.moved();
            return true;
        }

        /** What is under {@code key}, made by {@code making} and put there where nothing is. */
        V computeIfAbsent(K key, Function<? super K, ? extends V> making) {
            V had = get(changes.admitted(key));
            if (had != null) {
                return had;
            }
            V made = making.apply(key);
            put(key, made);
            return made;
        }

        boolean isEmpty() {
            return held == null || held.isEmpty();
        }

        /** What it holds now, which changes as it does. */
        Map<K, V> view() {
            return held == null ? Map.of() : Collections.unmodifiableMap(held);
        }
    }
}
