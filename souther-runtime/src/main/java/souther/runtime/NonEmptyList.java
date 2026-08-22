package souther.runtime;

import java.util.ArrayList;
import java.util.List;

/**
 * A list guaranteed to hold at least one element (spec §algebraic-types). A runtime auxiliary type;
 * not writable as a field type in the DSL. Decode-error accumulation now lives in Raoh, so this
 * type carries no decode role — it remains available as a general non-empty list.
 *
 * @param head the first element
 * @param tail the remaining elements (possibly empty)
 * @param <T>  the element type
 */
public record NonEmptyList<T>(T head, List<T> tail) {

    public NonEmptyList {
        tail = List.copyOf(tail);
    }

    public static <T> NonEmptyList<T> of(T head) {
        return new NonEmptyList<>(head, List.of());
    }

    @SafeVarargs
    @SuppressWarnings("varargs")   // `rest` is handed straight to `List.of`, which is varargs too
    public static <T> NonEmptyList<T> of(T head, T... rest) {
        return new NonEmptyList<>(head, List.of(rest));
    }

    /** Returns all elements as a plain list, head first. */
    public List<T> toList() {
        var all = new ArrayList<T>(tail.size() + 1);
        all.add(head);
        all.addAll(tail);
        return List.copyOf(all);
    }

    public int size() {
        return 1 + tail.size();
    }
}
