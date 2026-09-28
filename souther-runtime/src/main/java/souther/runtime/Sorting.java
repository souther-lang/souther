package souther.runtime;

import org.jspecify.annotations.Nullable;

import java.util.Collection;
import java.util.Comparator;
import java.util.Objects;

/**
 * A stable sort over storage that holds as many elements as a {@code List} does.
 *
 * <p>A {@code List} holds as many elements as its size counts ({@link Capacity}), and it does not
 * keep them in one array. The host's own sorts do: {@code ArrayList.sort} and {@code Arrays.sort}
 * sort an array, and a VM refuses an array a few elements short of what a size counts, whatever
 * the heap. A sort that went through one would refuse a list the language holds for want of an
 * intermediate it chose, which is the refusal the language rules out
 * (spec §an-operation-refuses-only-what-its-own-answer-has-no-place-for). So the elements are held
 * here in chunks, none of them longer than {@link #CHUNK}, and sorted by merging.
 *
 * <p>Stable: of two elements the order calls equal, the one first in the input is first in the
 * answer, as {@code List.sort} and {@code List.sortBy} state.
 */
final class Sorting {

    private static final int CHUNK_BITS = 16;
    private static final int CHUNK = 1 << CHUNK_BITS;
    private static final int CHUNK_MASK = CHUNK - 1;

    /** How long a run is sorted by insertion before runs are merged. */
    private static final int RUN = 32;

    private Sorting() {}

    /** {@code xs} in {@code order}, stably, as a new list; {@code xs} is left as it was. */
    @SuppressWarnings("unchecked")
    static <T> PersistentVector<T> stably(Collection<? extends T> xs, Comparator<? super T> order) {
        int n = xs.size();
        Slots from = new Slots(n);
        int at = 0;
        for (T x : xs) {
            from.set(at++, x);
        }
        for (long lo = 0; lo < n; lo += RUN) {
            insertionSort(from, (int) lo, (int) Math.min(lo + RUN, n), (Comparator<Object>) order);
        }
        Slots to = new Slots(n);
        for (long width = RUN; width < n; width *= 2) {
            for (long lo = 0; lo < n; lo += 2 * width) {
                int mid = (int) Math.min(lo + width, n);
                int hi = (int) Math.min(lo + 2 * width, n);
                merge(from, to, (int) lo, mid, hi, (Comparator<Object>) order);
            }
            Slots merged = to;
            to = from;
            from = merged;
        }
        PersistentVector.Builder<T> out = new PersistentVector.Builder<>();
        for (int i = 0; i < n; i++) {
            out.add((T) from.get(i));
        }
        return out.build();
    }

    /** Sorts {@code [lo, hi)} of {@code slots} in place; an element moves left only past one the
     *  order puts strictly after it, which is what keeps equal elements in their order. */
    private static void insertionSort(Slots slots, int lo, int hi, Comparator<Object> order) {
        for (int i = lo + 1; i < hi; i++) {
            Object x = slots.get(i);
            int j = i;
            while (j > lo && order.compare(slots.get(j - 1), x) > 0) {
                slots.set(j, slots.get(j - 1));
                j--;
            }
            slots.set(j, x);
        }
    }

    /** Merges the sorted {@code [lo, mid)} and {@code [mid, hi)} of {@code from} into the same
     *  places of {@code to}, taking from the left run on a tie. */
    private static void merge(Slots from, Slots to, int lo, int mid, int hi, Comparator<Object> order) {
        int left = lo;
        int right = mid;
        for (int out = lo; out < hi; out++) {
            if (right >= hi || (left < mid && order.compare(from.get(left), from.get(right)) <= 0)) {
                to.set(out, from.get(left++));
            } else {
                to.set(out, from.get(right++));
            }
        }
    }

    /** As many places as a size counts, held in chunks no longer than {@link #CHUNK}. Every place is
     *  written before it is read — the sort fills all of them first — so a read finds a value. */
    private static final class Slots {

        private final @Nullable Object[][] chunks;

        Slots(int size) {
            int count = (int) (((long) size + CHUNK - 1) >>> CHUNK_BITS);
            chunks = new @Nullable Object[count][];
            for (int i = 0; i < count; i++) {
                chunks[i] = new @Nullable Object[(int) Math.min(CHUNK, (long) size - ((long) i << CHUNK_BITS))];
            }
        }

        Object get(int i) {
            return Objects.requireNonNull(chunks[i >>> CHUNK_BITS][i & CHUNK_MASK]);
        }

        void set(int i, Object value) {
            chunks[i >>> CHUNK_BITS][i & CHUNK_MASK] = value;
        }
    }
}
