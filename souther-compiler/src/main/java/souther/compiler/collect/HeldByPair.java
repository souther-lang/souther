package souther.compiler.collect;

import java.util.concurrent.atomic.AtomicReferenceArray;
import java.util.function.BiFunction;
import java.util.function.Predicate;

/**
 * What was made for a pair last, kept by the two of it, so that asking again for an equal pair hands
 * out what was made and makes nothing — not even the pair.
 *
 * <p>For a value that is a function of two operands alone, asked for over and over with few pairs:
 * the answer of an operation of the exact arithmetic, which a compile asks of the same coefficients
 * and bounds in every form that holds them. {@link HeldByKey} would ask for a key made of the two,
 * and an ask that finds what it wants would still make that key; this is asked with the two as they
 * are.
 *
 * <p>The table is {@link HeldByKey}'s: it never grows and is never emptied, a pair falls in one set of
 * two slots with the one asked most recently in the first, and a pair no longer in its set is only
 * made and kept again. The order of the pair is part of it: {@code (a, b)} and {@code (b, a)} are two
 * pairs.
 *
 * <p>Slots are held strongly, as {@link HeldByKey}'s are and for the same reason, so a kind kept here
 * refers to nothing a compile is made of. The caller says which values are kept, since the slots
 * bound only their number and not the bytes each holds: a value {@code keeps} refuses is handed out
 * and not kept, and is made again at the next ask.
 *
 * <p>Written and read without a lock. An entry is immutable and published whole through the array,
 * and two threads filling one set leave the entry of one of them in it.
 *
 * @param <A> the first of the pair, immutable and equal by what it holds
 * @param <B> the second of the pair, the same
 * @param <V> the value, immutable, and the same for equal pairs
 */
public final class HeldByPair<A, B, V> {

    private record Entry<A, B, V>(A first, B second, V value) {}

    private final AtomicReferenceArray<Entry<A, B, V>> slots;
    private final int sets;

    /** As many sets as two to {@code bits}, of two slots each. */
    public HeldByPair(int bits) {
        if (bits < 1 || bits > 24) {
            throw new IllegalArgumentException("a table of two to " + bits + " sets");
        }
        this.sets = 1 << bits;
        this.slots = new AtomicReferenceArray<>(2 * sets);
    }

    /**
     * What is kept for a pair equal to {@code first} and {@code second}, or what {@code make} makes of
     * them — kept from now on where {@code keeps} says so.
     */
    public V get(A first, B second, BiFunction<? super A, ? super B, ? extends V> make,
            Predicate<? super V> keeps) {
        int at = 2 * HeldOnce.slotOf(31 * first.hashCode() + second.hashCode(), sets);
        Entry<A, B, V> newest = slots.get(at);
        if (newest != null && newest.first().equals(first) && newest.second().equals(second)) {
            return newest.value();
        }
        Entry<A, B, V> older = slots.get(at + 1);
        if (older != null && older.first().equals(first) && older.second().equals(second)) {
            slots.set(at, older);
            slots.set(at + 1, newest);
            return older.value();
        }
        V made = make.apply(first, second);
        if (keeps.test(made)) {
            slots.set(at + 1, newest);
            slots.set(at, new Entry<>(first, second, made));
        }
        return made;
    }
}
