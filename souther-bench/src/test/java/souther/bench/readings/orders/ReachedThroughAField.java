package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * A reader handed nothing, which meets a copy only in a field another method put it in.
 *
 * <p>Nothing calls the reader and it calls nothing, so the only thing that says it is to be read is
 * that the field it reads holds what came out of a copy.
 */
public final class ReachedThroughAField {

    private static Set<CompositionBudget> kept = Set.of();

    private ReachedThroughAField() {}

    public static void keep(List<CompositionBudget> figures) {
        kept = Set.copyOf(figures);
    }

    public static List<CompositionBudget> listed() {
        return new ArrayList<>(kept);
    }
}
