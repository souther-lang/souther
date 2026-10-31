package souther.compiler.collect;

import java.util.AbstractCollection;
import java.util.AbstractList;
import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.RandomAccess;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Unmodifiable copies of a map or a set that keep the order they were built in, held in as little
 * as such a copy can be.
 *
 * <p>{@code Map.copyOf} and {@code Set.copyOf} do not keep the order, and the order is read: what
 * a report writes first, which error a compile names first. An unmodifiable view over a
 * {@code LinkedHashMap} keeps it, and holds a table of at least sixteen slots, an entry object of
 * five fields for every key, and the view, which for the few keys most of these maps have is many
 * times what the keys and values are.
 *
 * <p>So the entries are held as CPython has held a dictionary since 3.6: keys and values side by
 * side in one array in the order given, with each key's hash beside them, and a table of where each
 * hash leads only where there are enough keys for one to pay. Under that, a key is found by
 * looking along the hashes, which for a handful of keys is as quick as a table and holds nothing.
 *
 * <p>Everything a caller asks is answered as the view over a {@code LinkedHashMap} answers it: in
 * the order given, a null value held, a null key held and asked about, equal to any map or set of
 * the same entries and hashed as one, and every change refused.
 */
public final class InTheOrderGiven {

    private InTheOrderGiven() {}

    /** From this many entries on, a key is found through a table rather than along the hashes. */
    private static final int LOOKED_UP_FROM = 9;

    /** The copy of a map with no entries, which every such copy is. */
    private static final HeldMap<?, ?> NO_ENTRIES = new HeldMap<>(new Object[0], new int[0], null);

    /** The copy of a set with no elements, which every such copy is. */
    private static final HeldSet<?> NO_ELEMENTS = new HeldSet<>(new Object[0], new int[0], null);

    /** {@code map}'s entries, in its order. A copy made here is handed back as it is. */
    @SuppressWarnings("unchecked")
    public static <K, V> Map<K, V> map(Map<? extends K, ? extends V> map) {
        if (map instanceof Refusing<?, ?>) {
            return (Map<K, V>) map;
        }
        int size = map.size();
        if (size == 0) {
            return (Map<K, V>) NO_ENTRIES;
        }
        if (size == 1) {
            Map.Entry<? extends K, ? extends V> only = map.entrySet().iterator().next();
            return new OneEntry<>(only.getKey(), only.getValue());
        }
        Object[] entries = new Object[size * 2];
        int[] hashes = new int[size];
        int at = 0;
        for (Map.Entry<? extends K, ? extends V> each : map.entrySet()) {
            entries[at * 2] = each.getKey();
            entries[at * 2 + 1] = each.getValue();
            hashes[at] = hashOf(each.getKey());
            at++;
        }
        if (at != size) {
            throw new IllegalStateException("a map said it held " + size + " entries and walked "
                    + at);
        }
        return new HeldMap<>(entries, hashes, tableOf(hashes));
    }

    /** {@code set}'s elements, in its order. A copy made here is handed back as it is. */
    @SuppressWarnings("unchecked")
    public static <T> Set<T> set(Collection<? extends T> set) {
        if (set instanceof HeldSet<?> held) {
            return (Set<T>) held;
        }
        int size = set.size();
        if (size == 0) {
            return (Set<T>) NO_ELEMENTS;
        }
        Object[] elements = new Object[size];
        int[] hashes = new int[size];
        int at = 0;
        for (T each : set) {
            elements[at] = each;
            hashes[at] = hashOf(each);
            at++;
        }
        if (at != size) {
            throw new IllegalStateException("a set said it held " + size + " elements and walked "
                    + at);
        }
        return new HeldSet<>(elements, hashes, tableOf(hashes));
    }

    /** A key's hash spread as {@code HashMap} spreads it, so its low bits say something. */
    private static int hashOf(Object key) {
        int hash = Objects.hashCode(key);
        return hash ^ (hash >>> 16);
    }

    /**
     * Where each hash leads, or null where there are too few for a table to pay: slot by slot, one
     * more than the position of a key with a hash that leads there, or nought where none does.
     */
    private static int[] tableOf(int[] hashes) {
        if (hashes.length < LOOKED_UP_FROM) {
            return null;
        }
        // Between a third and two thirds full, so a key not held meets an empty slot soon.
        int[] table = new int[Integer.highestOneBit(hashes.length + hashes.length / 2) * 2];
        int mask = table.length - 1;
        for (int at = 0; at < hashes.length; at++) {
            int slot = hashes[at] & mask;
            while (table[slot] != 0) {
                slot = (slot + 1) & mask;
            }
            table[slot] = at + 1;
        }
        return table;
    }

    /** The position of {@code key} among {@code keys} read every {@code stride}, or -1. */
    private static int positionOf(Object key, Object[] keys, int stride, int[] hashes,
                                  int[] table) {
        int hash = hashOf(key);
        if (table == null) {
            for (int at = 0; at < hashes.length; at++) {
                if (hashes[at] == hash && Objects.equals(keys[at * stride], key)) {
                    return at;
                }
            }
            return -1;
        }
        int mask = table.length - 1;
        for (int slot = hash & mask; table[slot] != 0; slot = (slot + 1) & mask) {
            int at = table[slot] - 1;
            if (hashes[at] == hash && Objects.equals(keys[at * stride], key)) {
                return at;
            }
        }
        return -1;
    }

    private static final class HeldMap<K, V> extends Refusing<K, V> {

        /** Each key followed by its value, in the order given. */
        private final Object[] entries;
        private final int[] hashes;
        private final int[] table;

        HeldMap(Object[] entries, int[] hashes, int[] table) {
            this.entries = entries;
            this.hashes = hashes;
            this.table = table;
        }

        @Override
        List<K> keysInOrder() {
            return new KeysOf<>(entries);
        }

        @Override
        public int size() {
            return hashes.length;
        }

        @Override
        public boolean isEmpty() {
            return hashes.length == 0;
        }

        @Override
        public boolean containsKey(Object key) {
            return positionOf(key, entries, 2, hashes, table) >= 0;
        }

        @Override
        @SuppressWarnings("unchecked")
        public V get(Object key) {
            int at = positionOf(key, entries, 2, hashes, table);
            return at < 0 ? null : (V) entries[at * 2 + 1];
        }

        @Override
        @SuppressWarnings("unchecked")
        public V getOrDefault(Object key, V otherwise) {
            int at = positionOf(key, entries, 2, hashes, table);
            return at < 0 ? otherwise : (V) entries[at * 2 + 1];
        }

        @Override
        public boolean containsValue(Object value) {
            for (int at = 1; at < entries.length; at += 2) {
                if (Objects.equals(entries[at], value)) {
                    return true;
                }
            }
            return false;
        }

        @Override
        @SuppressWarnings("unchecked")
        public void forEach(BiConsumer<? super K, ? super V> action) {
            for (int at = 0; at < entries.length; at += 2) {
                action.accept((K) entries[at], (V) entries[at + 1]);
            }
        }

        @Override
        public Set<Map.Entry<K, V>> entrySet() {
            return new AbstractSet<>() {
                @Override
                public int size() {
                    return hashes.length;
                }

                @Override
                @SuppressWarnings("unchecked")
                public Iterator<Map.Entry<K, V>> iterator() {
                    return new Along<>(hashes.length, at -> new SimpleImmutableEntry<>(
                            (K) entries[at * 2], (V) entries[at * 2 + 1]));
                }
            };
        }

        @Override
        public Set<K> keySet() {
            return new AbstractSet<>() {
                @Override
                public int size() {
                    return hashes.length;
                }

                @Override
                public boolean contains(Object key) {
                    return containsKey(key);
                }

                @Override
                @SuppressWarnings("unchecked")
                public Iterator<K> iterator() {
                    return new Along<>(hashes.length, at -> (K) entries[at * 2]);
                }

                @Override
                @SuppressWarnings("unchecked")
                public void forEach(Consumer<? super K> action) {
                    for (int at = 0; at < entries.length; at += 2) {
                        action.accept((K) entries[at]);
                    }
                }
            };
        }

        @Override
        public Collection<V> values() {
            return new AbstractCollection<>() {
                @Override
                public int size() {
                    return hashes.length;
                }

                @Override
                @SuppressWarnings("unchecked")
                public Iterator<V> iterator() {
                    return new Along<>(hashes.length, at -> (V) entries[at * 2 + 1]);
                }

                @Override
                @SuppressWarnings("unchecked")
                public void forEach(Consumer<? super V> action) {
                    for (int at = 1; at < entries.length; at += 2) {
                        action.accept((V) entries[at]);
                    }
                }
            };
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) {
                return true;
            }
            if (!(other instanceof Map<?, ?> that) || that.size() != hashes.length) {
                return false;
            }
            for (int at = 0; at < entries.length; at += 2) {
                Object value = entries[at + 1];
                Object theirs = that.get(entries[at]);
                if (theirs == null ? value != null || !that.containsKey(entries[at])
                        : !theirs.equals(value)) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public int hashCode() {
            int hash = 0;
            for (int at = 0; at < entries.length; at += 2) {
                hash += Objects.hashCode(entries[at]) ^ Objects.hashCode(entries[at + 1]);
            }
            return hash;
        }
    }

    /**
     * The keys of {@code map} in its order, as a list. Of a copy made here, the keys where they
     * are held, read in place and not copied: a form's terms are walked as a list every time a
     * row is read at it, and a copy of them each time is as many arrays as rows.
     */
    public static <K> List<K> keys(Map<K, ?> map) {
        return map instanceof Refusing<K, ?> held ? held.keysInOrder()
                : List.copyOf(map.keySet());
    }

    /** The keys of a {@link HeldMap}'s entries, every other one of them, read where they are. */
    private static final class KeysOf<K> extends AbstractList<K> implements RandomAccess {

        private final Object[] entries;

        KeysOf(Object[] entries) {
            this.entries = entries;
        }

        @Override
        @SuppressWarnings("unchecked")
        public K get(int at) {
            Objects.checkIndex(at, size());
            return (K) entries[at * 2];
        }

        @Override
        public int size() {
            return entries.length / 2;
        }
    }

    /** A map every change to which is refused, whether or not it would have changed it. */
    private abstract static class Refusing<K, V> extends AbstractMap<K, V> {

        /** The keys in the order given, read where they are held. */
        abstract List<K> keysInOrder();

        @Override
        public V put(K key, V value) {
            throw refused();
        }

        @Override
        public V remove(Object key) {
            throw refused();
        }

        @Override
        public void putAll(Map<? extends K, ? extends V> other) {
            throw refused();
        }

        @Override
        public void clear() {
            throw refused();
        }

        @Override
        public V putIfAbsent(K key, V value) {
            throw refused();
        }

        @Override
        public boolean remove(Object key, Object value) {
            throw refused();
        }

        @Override
        public boolean replace(K key, V oldValue, V newValue) {
            throw refused();
        }

        @Override
        public V replace(K key, V value) {
            throw refused();
        }

        @Override
        public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
            throw refused();
        }

        @Override
        public V computeIfAbsent(K key, Function<? super K, ? extends V> mapping) {
            throw refused();
        }

        @Override
        public V computeIfPresent(K key,
                                  BiFunction<? super K, ? super V, ? extends V> remapping) {
            throw refused();
        }

        @Override
        public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remapping) {
            throw refused();
        }

        @Override
        public V merge(K key, V value,
                       BiFunction<? super V, ? super V, ? extends V> remapping) {
            throw refused();
        }
    }

    /**
     * A copy of one entry: the key and the value and nothing else, which is what most of the maps
     * a compile holds for long are — a form over one number, a bound on one position.
     */
    private static final class OneEntry<K, V> extends Refusing<K, V> {

        private final K key;
        private final V value;

        OneEntry(K key, V value) {
            this.key = key;
            this.value = value;
        }

        @Override
        List<K> keysInOrder() {
            return Collections.singletonList(key);
        }

        @Override
        public int size() {
            return 1;
        }

        @Override
        public boolean isEmpty() {
            return false;
        }

        @Override
        public boolean containsKey(Object asked) {
            return Objects.equals(key, asked);
        }

        @Override
        public V get(Object asked) {
            return Objects.equals(key, asked) ? value : null;
        }

        @Override
        public V getOrDefault(Object asked, V otherwise) {
            return Objects.equals(key, asked) ? value : otherwise;
        }

        @Override
        public boolean containsValue(Object asked) {
            return Objects.equals(value, asked);
        }

        @Override
        public void forEach(BiConsumer<? super K, ? super V> action) {
            action.accept(key, value);
        }

        @Override
        public Set<Map.Entry<K, V>> entrySet() {
            return new AbstractSet<>() {
                @Override
                public int size() {
                    return 1;
                }

                @Override
                public Iterator<Map.Entry<K, V>> iterator() {
                    return new Along<>(1, at -> new SimpleImmutableEntry<>(key, value));
                }
            };
        }

        @Override
        public Set<K> keySet() {
            return new AbstractSet<>() {
                @Override
                public int size() {
                    return 1;
                }

                @Override
                public boolean contains(Object asked) {
                    return Objects.equals(key, asked);
                }

                @Override
                public Iterator<K> iterator() {
                    return new Along<>(1, at -> key);
                }
            };
        }

        @Override
        public Collection<V> values() {
            return new AbstractCollection<>() {
                @Override
                public int size() {
                    return 1;
                }

                @Override
                public Iterator<V> iterator() {
                    return new Along<>(1, at -> value);
                }
            };
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) {
                return true;
            }
            if (!(other instanceof Map<?, ?> that) || that.size() != 1) {
                return false;
            }
            Object theirs = that.get(key);
            return theirs == null ? value == null && that.containsKey(key) : theirs.equals(value);
        }

        @Override
        public int hashCode() {
            return Objects.hashCode(key) ^ Objects.hashCode(value);
        }
    }

    /** What every change to a copy made here says, whether or not it would have changed it. */
    private static UnsupportedOperationException refused() {
        return new UnsupportedOperationException("a copy kept in the order given is not changed");
    }

    private static final class HeldSet<T> extends AbstractSet<T> {

        private final Object[] elements;
        private final int[] hashes;
        private final int[] table;

        HeldSet(Object[] elements, int[] hashes, int[] table) {
            this.elements = elements;
            this.hashes = hashes;
            this.table = table;
        }

        @Override
        public int size() {
            return elements.length;
        }

        @Override
        public boolean isEmpty() {
            return elements.length == 0;
        }

        @Override
        public boolean contains(Object element) {
            return positionOf(element, elements, 1, hashes, table) >= 0;
        }

        @Override
        @SuppressWarnings("unchecked")
        public Iterator<T> iterator() {
            return new Along<>(elements.length, at -> (T) elements[at]);
        }

        @Override
        @SuppressWarnings("unchecked")
        public void forEach(Consumer<? super T> action) {
            for (Object each : elements) {
                action.accept((T) each);
            }
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) {
                return true;
            }
            if (!(other instanceof Set<?> that) || that.size() != elements.length) {
                return false;
            }
            for (Object each : elements) {
                if (!that.contains(each)) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public int hashCode() {
            int hash = 0;
            for (Object each : elements) {
                hash += Objects.hashCode(each);
            }
            return hash;
        }

        @Override
        public boolean add(T element) {
            throw refused();
        }

        @Override
        public boolean remove(Object element) {
            throw refused();
        }

        @Override
        public boolean addAll(Collection<? extends T> other) {
            throw refused();
        }

        @Override
        public boolean removeAll(Collection<?> other) {
            throw refused();
        }

        @Override
        public boolean retainAll(Collection<?> other) {
            throw refused();
        }

        @Override
        public boolean removeIf(Predicate<? super T> filter) {
            throw refused();
        }

        @Override
        public void clear() {
            throw refused();
        }
    }

    /** What stands at each position in turn, made as it is reached. */
    private static final class Along<T> implements Iterator<T> {

        /** What stands at a position. */
        interface At<T> {
            T at(int position);
        }

        private final int size;
        private final At<T> at;
        private int next;

        Along(int size, At<T> at) {
            this.size = size;
            this.at = at;
        }

        @Override
        public boolean hasNext() {
            return next < size;
        }

        @Override
        public T next() {
            if (next >= size) {
                throw new NoSuchElementException();
            }
            return at.at(next++);
        }
    }
}
