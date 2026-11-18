package souther.compiler.partition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * What a reading only adds to, with a revision that says which history of additions it stands at
 * and a checkpoint it can be rewound to.
 *
 * <p>The revision identifies a history and not a content: it is this ledger with a number drawn
 * from a count that is never taken back, and every addition draws a new one. Two ledgers, or two
 * histories of one ledger that hold the same, have different revisions, so a revision that is the
 * same says the ledger is where it was and a revision that differs says nothing of what it holds.
 * A checkpoint is how many entries there were and the revision; rewinding takes off the entries
 * after it and puts the revision back, and the count is not put back, so what is added after a
 * rewind never stands at a revision anything stood at before.
 *
 * <p>A checkpoint is rewound to only while it is on the history: while the entry it ended at is the
 * one there now. One taken on a branch that was rewound past is refused, since taking entries off
 * cannot put back the ones that were taken off.
 *
 * <p>Nothing adds to it but its own methods: what it hands out cannot be changed through. It
 * holds no null: an entry is something added, and whether a key is held is whether it was put.
 */
abstract sealed class Ledger implements ReadingState.Marked
        permits Ledger.OfEntries, Ledger.Keyed, Ledger.Grouped {

    /** Which history a ledger stands at: compared by the very ledger and the number, which is all
     *  a comparison of it looks at. */
    record Revision(Ledger of, long number) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Revision that && that.of == of && that.number == number;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(of) * 31 + Long.hashCode(number);
        }
    }

    /** Where a ledger stood, to be rewound to. */
    static final class Checkpoint {
        private final Ledger of;
        private final int size;
        private final long revision;

        private Checkpoint(Ledger of, int size, long revision) {
            this.of = of;
            this.size = size;
            this.revision = revision;
        }
    }

    /** The last number drawn, which only grows. */
    private long drawn;
    /** The revision the ledger stood at after each entry. */
    private long[] stamps = new long[4];
    private int size;
    /** The revision now: that of the last entry, or nought where there is none. */
    private long revision;

    /** That one more entry has been added. */
    final void added() {
        if (size == stamps.length) {
            stamps = Arrays.copyOf(stamps, size * 2);
        }
        revision = ++drawn;
        stamps[size++] = revision;
    }

    /** Where this stands now. */
    final Checkpoint checkpoint() {
        return new Checkpoint(this, size, revision);
    }

    /**
     * Takes off what was added after {@code checkpoint}, which is on the history of this.
     *
     * @throws IllegalStateException where it is a checkpoint of another ledger, or of a branch
     *         this was rewound past
     */
    final void rewind(Checkpoint checkpoint) {
        if (checkpoint.of != this || checkpoint.size > size
                || (checkpoint.size == 0 ? 0 : stamps[checkpoint.size - 1]) != checkpoint.revision) {
            throw new IllegalStateException("a checkpoint off the history of this ledger");
        }
        takeOffFrom(checkpoint.size);
        size = checkpoint.size;
        revision = checkpoint.revision;
    }

    /** Takes off the entries from the {@code from}th on. */
    abstract void takeOffFrom(int from);

    /** What it holds, as the collection a comparison of what it holds is made of. */
    abstract Object contents();

    /** What it holds as a value that a later addition does not reach, each entry the very object
     *  it is: what a reading that asked what it holds is compared on. */
    abstract Object asItHolds();

    @Override
    public final Object mark() {
        return new Revision(this, revision);
    }

    /** Entries in the order they were added. */
    static final class OfEntries<E> extends Ledger {

        private final List<E> held = new ArrayList<>();

        void add(E entry) {
            held.add(Objects.requireNonNull(entry, "an entry is something added"));
            added();
        }

        void addAll(Collection<? extends E> each) {
            for (E one : each) {
                add(one);
            }
        }

        boolean isEmpty() {
            return held.isEmpty();
        }

        /** What it holds now, which changes as it does. */
        List<E> view() {
            return Collections.unmodifiableList(held);
        }

        @Override
        void takeOffFrom(int from) {
            held.subList(from, held.size()).clear();
        }

        @Override
        Object contents() {
            return held;
        }

        @Override
        Object asItHolds() {
            return ReadingState.theVeryOnes(held);
        }
    }

    /** Values each under a key, the first put under a key the one it keeps. */
    static final class Keyed<K, V> extends Ledger {

        private final Map<K, V> held = new LinkedHashMap<>();
        private final List<K> order = new ArrayList<>();

        /** Puts {@code value} under {@code key} where nothing is, and answers what is. */
        V putIfAbsent(K key, V value) {
            V had = held.putIfAbsent(Objects.requireNonNull(key, "a key is something put"),
                    Objects.requireNonNull(value, "a value is something put"));
            if (had == null) {
                order.add(key);
                added();
            }
            return had;
        }

        V get(Object key) {
            return held.get(key);
        }

        Set<K> keys() {
            return Collections.unmodifiableSet(held.keySet());
        }

        /** What it holds now, which changes as it does. */
        Map<K, V> view() {
            return Collections.unmodifiableMap(held);
        }

        @Override
        void takeOffFrom(int from) {
            List<K> after = order.subList(from, order.size());
            after.forEach(held::remove);
            after.clear();
        }

        @Override
        Object contents() {
            return held;
        }

        @Override
        Object asItHolds() {
            Map<Object, Object> out = new HashMap<>();
            held.forEach((key, value) -> out.put(ReadingState.theVeryOne(key),
                    ReadingState.theVeryOne(value)));
            return out;
        }
    }

    /** Values gathered under each key, in the order they were added. */
    static final class Grouped<K, V> extends Ledger {

        private final Map<K, List<V>> held = new LinkedHashMap<>();
        private final List<K> order = new ArrayList<>();

        void add(K key, V value) {
            Objects.requireNonNull(key, "a key is something put");
            Objects.requireNonNull(value, "a value is something added");
            held.computeIfAbsent(key, _ -> new ArrayList<>()).add(value);
            order.add(key);
            added();
        }

        boolean isEmpty() {
            return held.isEmpty();
        }

        Set<K> keys() {
            return Collections.unmodifiableSet(held.keySet());
        }

        /** What is gathered under {@code key}, which changes as it does. */
        List<V> under(K key) {
            return Collections.unmodifiableList(held.getOrDefault(key, List.of()));
        }

        @Override
        void takeOffFrom(int from) {
            for (int at = order.size() - 1; at >= from; at--) {
                K key = order.remove(at);
                List<V> under = held.get(key);
                under.removeLast();
                if (under.isEmpty()) {
                    held.remove(key);
                }
            }
        }

        @Override
        Object contents() {
            return held;
        }

        @Override
        Object asItHolds() {
            Map<Object, Object> out = new HashMap<>();
            held.forEach((key, under) -> out.put(ReadingState.theVeryOne(key),
                    ReadingState.theVeryOnes(under)));
            return out;
        }
    }
}
