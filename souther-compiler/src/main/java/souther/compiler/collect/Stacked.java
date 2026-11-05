package souther.compiler.collect;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * Things in the order they came, where one more is another of these on top of this one, which is
 * left as it was and shared.
 *
 * <p>For what a walk keeps of what it took in and reads only at the end: one more costs one, and
 * the order is written out when it is asked for ({@link #inOrder}). Two of these put on one are
 * two, each reading what was under it and nothing of the other.
 *
 * @param <T> what is put on, never null
 */
public final class Stacked<T> {

    private static final Stacked<?> EMPTY = new Stacked<>(null, null, 0);

    private final T last;
    private final Stacked<T> under;
    private final int size;

    private Stacked(T last, Stacked<T> under, int size) {
        this.last = last;
        this.under = under;
        this.size = size;
    }

    /** Nothing. */
    @SuppressWarnings("unchecked")
    public static <T> Stacked<T> empty() {
        return (Stacked<T>) EMPTY;
    }

    /** These and {@code next} after them. */
    public Stacked<T> then(T next) {
        Objects.requireNonNull(next, "what is put on is something");
        return new Stacked<>(next, this, size + 1);
    }

    /** How many were put on. */
    public int size() {
        return size;
    }

    /** Every one, the first put on first. */
    public List<T> inOrder() {
        List<T> out = new ArrayList<>(size);
        for (Stacked<T> at = this; at.size > 0; at = at.under) {
            out.add(at.last);
        }
        Collections.reverse(out);
        return Collections.unmodifiableList(out);
    }
}
