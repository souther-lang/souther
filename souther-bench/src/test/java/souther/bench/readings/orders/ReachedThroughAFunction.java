package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

/**
 * A reader handed nothing, which meets a copy only in what a function it made returns.
 *
 * <p>The copy is made in the function's body, which is a method of its own that nothing calls by
 * name. What says the reader is to be read is that it is where that function is made.
 */
public final class ReachedThroughAFunction {

    private ReachedThroughAFunction() {}

    public static List<CompositionBudget> listed() {
        Supplier<Set<CompositionBudget>> made =
                () -> Set.copyOf(List.of(CompositionBudget.values()));
        return new ArrayList<>(made.get());
    }
}
