package souther.runtime;

import org.jspecify.annotations.Nullable;

import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 * An immutable set backed by a {@link PersistentHashMap} whose values are a shared sentinel, so it
 * reuses the CHAMP trie, structural sharing, deterministic hash-order iteration, and value-equality
 * key handling. It implements {@link java.util.Set}, extending {@link AbstractSet} for the immutable,
 * mutator-throwing defaults and the order-INSENSITIVE {@code Set.equals}/{@code hashCode} that Souther
 * value equality (ADR-0009) relies on.
 *
 * <p>Iteration order is a deterministic, implementation-defined hash order (not first-seen order),
 * stable for the same element set so boundary encoding stays reproducible.
 *
 * <p>A dedicated key-only CHAMP node (no value slots) would save memory; the sentinel-map form is
 * behaviorally identical and is the minimal first cut.
 */
public final class PersistentHashSet<E> extends AbstractSet<E> {

    private static final Object PRESENT = new Object();

    public static final PersistentHashSet<?> EMPTY =
            new PersistentHashSet<>(PersistentHashMap.empty());

    private final PersistentHashMap<E, Object> map;

    private PersistentHashSet(PersistentHashMap<E, Object> map) {
        this.map = map;
    }

    @SuppressWarnings("unchecked")
    public static <E> PersistentHashSet<E> empty() {
        return (PersistentHashSet<E>) EMPTY;
    }

    public static <E> PersistentHashSet<E> ofSingle(E value) {
        return PersistentHashSet.<E>empty().with(value);
    }

    /** Wraps {@code src} as a PersistentHashSet, sharing when it already is one, else building by
     *  adding each element (dropping duplicates). */
    @SuppressWarnings("unchecked")
    public static <E> PersistentHashSet<E> from(Collection<? extends E> src) {
        if (src instanceof PersistentHashSet<?> phs) {
            return (PersistentHashSet<E>) phs;
        }
        return build(src.iterator());
    }

    /** Drains {@code elements} into a set in one pass, through the backing map's bulk builder: the
     *  trie never leaves this method, so its nodes are filled in place rather than cloned per
     *  element. Every set operation that produces a fresh set goes through here. */
    private static <E> PersistentHashSet<E> build(java.util.Iterator<? extends E> elements) {
        PersistentHashMap.Builder<E, Object> b = new PersistentHashMap.Builder<>();
        while (elements.hasNext()) {
            b.put(elements.next(), PRESENT);
        }
        PersistentHashMap<E, Object> m = b.build();
        return m.isEmpty() ? empty() : new PersistentHashSet<>(m);
    }

    /** This set with {@code value} added (unchanged when already present). */
    public PersistentHashSet<E> with(E value) {
        PersistentHashMap<E, Object> m = map.assoc(value, PRESENT);
        return m == map ? this : new PersistentHashSet<>(m);
    }

    /** This set without {@code value} (unchanged when absent). */
    public PersistentHashSet<E> without(E value) {
        PersistentHashMap<E, Object> m = map.without(value);
        return m == map ? this : new PersistentHashSet<>(m);
    }

    @Override
    public int size() {
        return map.size();
    }

    @Override
    public boolean contains(@Nullable Object value) {
        return map.containsKey(value);
    }

    @Override
    public Iterator<E> iterator() {
        return map.keySet().iterator();
    }

    /** All elements of {@code a} and {@code b} (adds the smaller into the larger). */
    public static <E> PersistentHashSet<E> union(Set<? extends E> a, Set<? extends E> b) {
        Set<? extends E> larger = a.size() >= b.size() ? a : b;
        Set<? extends E> smaller = a.size() >= b.size() ? b : a;
        if (smaller.isEmpty()) {
            return from(larger);
        }
        PersistentHashMap.Builder<E, Object> out = new PersistentHashMap.Builder<>();
        for (E e : larger) {
            out.put(e, PRESENT);
        }
        for (E e : smaller) {
            out.put(e, PRESENT);
        }
        PersistentHashMap<E, Object> m = out.build();
        return m.isEmpty() ? empty() : new PersistentHashSet<>(m);
    }

    /** The elements in both {@code a} and {@code b} (scans the smaller). */
    public static <E> PersistentHashSet<E> intersect(Set<? extends E> a, Set<? extends E> b) {
        Set<?> larger = a.size() >= b.size() ? a : b;
        Set<? extends E> smaller = a.size() >= b.size() ? b : a;
        List<E> kept = new ArrayList<>();
        for (E e : smaller) {
            if (larger.contains(e)) {
                kept.add(e);
            }
        }
        return kept.isEmpty() ? empty() : build(kept.iterator());
    }

    /** The elements of {@code a} that are not in {@code b}. */
    public static <E> PersistentHashSet<E> difference(Set<? extends E> a, Set<? extends E> b) {
        if (b.isEmpty()) {
            return from(a);
        }
        List<E> kept = new ArrayList<>();
        for (E e : a) {
            if (!b.contains(e)) {
                kept.add(e);
            }
        }
        return kept.isEmpty() ? empty() : build(kept.iterator());
    }
}
