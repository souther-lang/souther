package souther.compiler.collect;

import java.util.concurrent.atomic.AtomicReferenceArray;
import java.util.function.Function;

/**
 * What was made for a key last, kept by the key, so that asking again for an equal key hands out
 * what was made and makes nothing.
 *
 * <p>For a value that is a function of its key alone, asked for over and over with few keys: the
 * exact ratio of a decimal, which a compile asks for in every form that holds the decimal. {@link
 * HeldOnce} shares what was already made and so cannot spare the making; this spares it.
 *
 * <p>The table never grows and is never emptied. A key falls in one set of two slots, the one asked
 * most recently in the first, and a key that is no longer in its set is only made and kept again,
 * so what this costs is the slots and what it can get wrong is nothing. Two slots and not one
 * because two keys that are asked for in turn and fall in the same set would otherwise take each
 * other's slot at every ask; a hash cannot always keep them apart, since distinct keys may hash
 * alike. A third such key still does, which is rare enough not to be paid for.
 *
 * <p>Slots are held strongly: what is kept has no other holder, and a weak slot would be cleared
 * before it was asked again. So a kind kept here refers to nothing a compile is made of, and the
 * caller bounds the size of what it keeps, since the slots bound only their number.
 *
 * <p>Written and read without a lock. An entry is immutable and published whole through the array,
 * and two threads filling one set leave the entry of one of them in it, which is only a key made
 * again by the next ask that does not find it.
 *
 * @param <K> the key, immutable and equal by what it holds
 * @param <V> the value, immutable, and the same for equal keys
 */
public final class HeldByKey<K, V> {

    private record Entry<K, V>(K key, V value) {}

    private final AtomicReferenceArray<Entry<K, V>> slots;
    private final int sets;

    /** As many sets as two to {@code bits}, of two slots each. */
    public HeldByKey(int bits) {
        if (bits < 1 || bits > 24) {
            throw new IllegalArgumentException("a table of two to " + bits + " sets");
        }
        this.sets = 1 << bits;
        this.slots = new AtomicReferenceArray<>(2 * sets);
    }

    /** What is kept for a key equal to {@code key}, or what {@code make} makes of it, kept from now on. */
    public V get(K key, Function<? super K, ? extends V> make) {
        int first = 2 * HeldOnce.slotOf(key.hashCode(), sets);
        Entry<K, V> newest = slots.get(first);
        if (newest != null && newest.key().equals(key)) {
            return newest.value();
        }
        Entry<K, V> older = slots.get(first + 1);
        if (older != null && older.key().equals(key)) {
            slots.set(first, older);
            slots.set(first + 1, newest);
            return older.value();
        }
        V made = make.apply(key);
        slots.set(first + 1, newest);
        slots.set(first, new Entry<>(key, made));
        return made;
    }
}
