package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * A reader handed nothing, which meets a copy only in a list a field holds it in.
 *
 * <p>The list is what the field holds, and the copy is an element of it; the reader takes the
 * copy out and puts its order in an answer.
 */
public final class HeldWholeInAField {

    private static final List<Set<CompositionBudget>> HOLDER = new ArrayList<>();

    private HeldWholeInAField() {}

    public static void keep(Set<CompositionBudget> values) {
        HOLDER.add(Set.copyOf(values));
    }

    public static List<CompositionBudget> takenOutElsewhere() {
        return new ArrayList<>(HOLDER.getFirst());
    }
}
