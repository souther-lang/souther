package souther.compiler.examples;

import souther.compiler.evaluate.EvaluationContext;
import souther.runtime.Tuple;

import java.lang.reflect.Method;
import java.lang.reflect.RecordComponent;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Map;

/**
 * Every node of a value an evaluation built, one counted point each, before the value is handed to
 * something that goes over the same nodes and counts none of them: the boundary library writing it
 * out through a derived encoder.
 *
 * <p>Apart from {@link ObservedValues}, which reads a value into the form a report holds and stops
 * where the report would not show more. A report's limits say how much of a value is worth showing;
 * what is paid for here is how much will be walked, which is all of it whatever is shown. The one
 * walk could not answer both without one of them reading the other's limit.
 *
 * <p>Walked with a stack of its own, so a value nested deeper than a thread's stack is still counted
 * rather than ending the walk in a way that says nothing about the value. A generated data class
 * and an optional are records, and are gone into through their components; a tuple through its
 * elements; a collection through what it holds. Everything else is one node.
 */
final class PaidForBeforeItIsWalked {

    private PaidForBeforeItIsWalked() {}

    /** Counts every node of {@code value}, throwing where the evaluation cannot afford them. */
    static void payFor(Object value) {
        Deque<Object> pending = new ArrayDeque<>();
        pending.push(value == null ? NOTHING : value);
        while (!pending.isEmpty()) {
            Object each = pending.pop();
            EvaluationContext.tick();
            switch (each) {
                case Map<?, ?> m -> m.forEach((k, v) -> {
                    pending.push(held(k));
                    pending.push(held(v));
                });
                case Iterable<?> elements -> elements.forEach(e -> pending.push(held(e)));
                case Tuple t -> {
                    for (int i = 0; i < t.size(); i++) {
                        pending.push(held(t.get(i)));
                    }
                }
                case Record r -> {
                    for (RecordComponent component : r.getClass().getRecordComponents()) {
                        pending.push(held(component(r, component.getAccessor())));
                    }
                }
                default -> { }
            }
        }
    }

    /** What stands in the walk for a null a value holds, which is a node and holds nothing. */
    private static final Object NOTHING = new Object();

    private static Object held(Object value) {
        return value == null ? NOTHING : value;
    }

    /** A component of a record, read through its accessor, which a generated class may not have
     *  made public; one that cannot be read is a node holding nothing. */
    private static Object component(Record r, Method accessor) {
        try {
            accessor.setAccessible(true);
            return accessor.invoke(r);
        } catch (ReflectiveOperationException | RuntimeException e) {
            EvaluationContext.rethrowIfOverspent(e);
            return NOTHING;
        }
    }
}
