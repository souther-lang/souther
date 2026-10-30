package souther.compiler.collect;

/**
 * The values of one kind made last, each in the slot its hash falls in, so that a value made again
 * while the one before it is still in its slot is handed out as that one.
 *
 * <p>For a kind of immutable value a compile makes over and over and holds for long: a ratio a form
 * weighs a term by, a word a spelling is made of, a condition's ways that every path through it
 * files again. Each held as one of its own, a few thousand values were a million objects. Handed
 * out from here, the copies made on the way die young and what is held is the one.
 *
 * <p>One slot per hash and the newest kept, as a direct-mapped cache keeps a line: this never grows
 * and is never emptied, and a value it no longer holds is only made and held again, so what it
 * costs is the slots and what it can get wrong is nothing. Equal values are one value to every
 * reader of a kind that is handed out here; a kind whose readers tell equal values apart by identity
 * does not belong here.
 *
 * <p>Written and read without a lock. The values are immutable with final fields, so a reader that
 * finds one finds it whole, and two threads filling one slot leave one of their values in it, which
 * is only a value held twice.
 *
 * @param <T> the kind of value, immutable and equal by what it holds
 */
public final class HeldOnce<T> {

    private final Object[] slots;

    /** As many slots as two to {@code bits}. */
    public HeldOnce(int bits) {
        if (bits < 1 || bits > 24) {
            throw new IllegalArgumentException("a table of two to " + bits + " slots");
        }
        this.slots = new Object[1 << bits];
    }

    /** The value equal to {@code made} that is held here, or {@code made}, held from now on. */
    @SuppressWarnings("unchecked")
    public T held(T made) {
        int hash = made.hashCode();
        int slot = (hash ^ (hash >>> 16)) & (slots.length - 1);
        Object there = slots[slot];
        if (there != null && there.equals(made)) {
            return (T) there;
        }
        slots[slot] = made;
        return made;
    }
}
