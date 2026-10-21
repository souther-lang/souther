package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * Readers handed nothing, which meet a copy only in what a method they call hands back.
 *
 * <p>What they hand the method is made of nothing from a copy, so the call is not one that carries
 * a copy in. The copy comes out: returned by one, and put into the list it was handed by the other.
 */
public final class ReachedThroughWhatACallHandsBack {

    private ReachedThroughWhatACallHandsBack() {}

    public static List<CompositionBudget> listedFromWhatIsReturned() {
        return new ArrayList<>(made(List.of(CompositionBudget.values())));
    }

    private static Set<CompositionBudget> made(List<CompositionBudget> figures) {
        return Set.copyOf(figures);
    }

    public static List<CompositionBudget> listedFromWhatIsFilledIn() {
        List<CompositionBudget> into = new ArrayList<>();
        fill(into, List.of(CompositionBudget.values()));
        return into;
    }

    private static void fill(List<CompositionBudget> into, List<CompositionBudget> figures) {
        for (CompositionBudget each : Set.copyOf(figures)) {
            into.add(each);
        }
    }
}
