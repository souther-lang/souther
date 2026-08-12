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
 * reuses the CHAMP trie, structural sharing, its iteration order, and value-equality key handling.
 * It implements {@link java.util.Set}, extending {@link AbstractSet} for the immutable,
 * mutator-throwing defaults.
 *
 * <p>Membership here is the language's. Two amounts that differ only in scale are one element, and
 * the trie is indexed by the hash that says so, so {@code contains} answers that question and cannot
 * answer another: there is one index, not two. {@code equals} and {@code hashCode} follow membership
 * rather than being inherited, because a set whose {@code contains} is the language's and whose hash
 * was the JDK's would call two sets equal and hash them apart.
 *
 * <p>The cost is stated rather than hidden: against a foreign {@code java.util.Set} holding the same
 * amount at another scale, {@code equals} is not symmetric — this one finds the element and the
 * other does not. Only Java interop can construct that pair; a set Souther built is compared with a
 * set Souther built. A {@link PersistentVector} keeps the {@code List} contract instead, because a
 * list compares positionally and has no index to be indexed by.
 *
 * <p>Iteration is a deterministic traversal of the backing trie, and the language specifies no order
 * at all (spec §stdlib-set). It is not first-seen order and must not be read as one. What the
 * determinism is <em>for</em> is a particular trie, not the set value: two sets that are equal are
 * not guaranteed to iterate in the same order, because elements sharing a full hash sit in one
 * collision bucket held in the order they were added (see {@link PersistentHashMap}). A caller must
 * therefore depend on no particular order. The boundary encoding does not: it puts the members in
 * the order their own external representations give ({@link Representations}), which is exactly the
 * order this traversal cannot promise.
 *
 * <p>A dedicated key-only CHAMP node (no value slots) would save memory; the sentinel-map form is
 * behaviorally identical and is the minimal first cut.
 */
public final class PersistentHashSet<E> extends AbstractSet<E> implements ValueSemantics {

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
            b.set(elements.next(), PRESENT);
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

    @Override
    public boolean equals(@Nullable Object o) {
        return valueEquals(o);
    }

    @Override
    public int hashCode() {
        return valueHash();
    }

    /**
     * Whether {@code o} holds the same elements the language means.
     *
     * <p>The other set is taken through {@link #from} first, because a foreign set is indexed by
     * Java's equality, which is finer than the language's: a {@code HashSet} of 1.0 and 1.00 has two
     * elements and the language sees one. Counted as it stands, both of those would find the same
     * element here and nothing would notice the element this set has that it does not. Normalized,
     * the sizes are the sizes the language means and one lookup each decides it. {@code from} shares
     * when the set already is one, so a set Souther built pays nothing.
     */
    @Override
    public boolean valueEquals(@Nullable Object o) {
        if (o == this) {
            return true;
        }
        if (!(o instanceof Set<?> s)) {
            return false;
        }
        PersistentHashSet<?> other = PersistentHashSet.from(s);
        if (other.size() != size()) {
            return false;
        }
        for (Object e : other) {
            if (!contains(e)) {
                return false;
            }
        }
        return true;
    }

    /** Summed over the elements, so it does not depend on the order they are walked in — a set is
     *  unordered, and two holding the same elements reach them in different places. */
    @Override
    public int valueHash() {
        int h = 0;
        for (E e : this) {
            h += Values.hash(e);
        }
        return h;
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
            out.set(e, PRESENT);
        }
        for (E e : smaller) {
            out.set(e, PRESENT);
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
