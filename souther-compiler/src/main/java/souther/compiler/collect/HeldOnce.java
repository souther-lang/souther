package souther.compiler.collect;

import java.lang.ref.WeakReference;
import java.util.function.Function;

/**
 * The values of one kind made last, each in the slot its hash falls in, so that a value made again
 * while the one before it is still in its slot and still held is handed out as that one.
 *
 * <p>For a kind of immutable value a compile makes over and over and holds for long: a ratio a form
 * weighs a term by, a word a spelling is made of, a condition's ways that every path through it
 * files again — a few distinct values made many times each. Handed out from here, the copies made
 * on the way die young and what is held is the one.
 *
 * <p>One slot per hash and the newest kept, as a direct-mapped cache keeps a line: this never grows
 * and is never emptied, and a value it no longer holds is only made and held again, so what it
 * costs is the slots and what it can get wrong is nothing. Equal values are one value to every
 * reader of a kind that is handed out here; a kind whose readers tell equal values apart by identity
 * does not belong here.
 *
 * <p>A slot refers to its value weakly, as the hash-consing tables of OCaml's {@code Weak} do: this
 * finds a value while something else holds it and keeps none alive. One of these is shared by every
 * compile a process makes, and a value a compile is done with may refer to all of that compile — a
 * condition's ways to the model they were read from, a place a run was seen at to the numbering of
 * every body. Held strongly, a slot would keep that for as long as the process runs.
 *
 * <p>Written and read without a lock. The values are immutable with final fields, so a reader that
 * finds one finds it whole, and two threads filling one slot leave one of their values in it, which
 * is only a value held twice.
 *
 * @param <T> the kind of value, immutable and equal by what it holds
 */
public final class HeldOnce<T> {

    private final WeakReference<?>[] slots;

    /** As many slots as two to {@code bits}. */
    public HeldOnce(int bits) {
        if (bits < 1 || bits > 24) {
            throw new IllegalArgumentException("a table of two to " + bits + " slots");
        }
        this.slots = new WeakReference<?>[1 << bits];
    }

    /** The value equal to {@code made} that is held here, or {@code made}, held from now on. */
    @SuppressWarnings("unchecked")
    public T held(T made) {
        int slot = slotOf(made.hashCode(), slots.length);
        WeakReference<?> at = slots[slot];
        Object there = at == null ? null : at.get();
        if (there != null && there.equals(made)) {
            return (T) there;
        }
        slots[slot] = new WeakReference<>(made);
        return made;
    }

    /**
     * The value held here whose key is {@code key}, or what {@code make} makes of it, held from now
     * on — so that a value found by what it is made of costs nothing to ask for.
     *
     * <p>For a kind whose value is a function of a key it holds, and is equal to another exactly
     * where their keys are equal: {@code keyOf} reads the key back off a value, and a value's hash
     * is its key's, which is what puts the two in one slot.
     */
    @SuppressWarnings("unchecked")
    public <K> T held(K key, Function<? super T, ?> keyOf, Function<? super K, ? extends T> make) {
        int slot = slotOf(key.hashCode(), slots.length);
        WeakReference<?> at = slots[slot];
        Object there = at == null ? null : at.get();
        if (there != null && keyOf.apply((T) there).equals(key)) {
            return (T) there;
        }
        T made = make.apply(key);
        slots[slot] = new WeakReference<>(made);
        return made;
    }

    /** The slot a hash falls in among {@code count}, a power of two: the high half of the hash is
     *  mixed into the low half, which is all a power of two reads. */
    static int slotOf(int hash, int count) {
        return (hash ^ (hash >>> 16)) & (count - 1);
    }
}
