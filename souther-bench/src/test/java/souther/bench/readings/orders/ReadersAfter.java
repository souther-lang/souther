package souther.bench.readings.orders;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.publish.PublicationOrders;

import java.util.ArrayList;
import java.util.List;

/**
 * Two readers of a copy, one of which was put in an order before it was read and one of which is
 * not.
 *
 * <p>The same number of readers as {@link ReadersBefore}, of the same copy. One is the reader it
 * was; the other is a reader that was written after the check was, and names nobody.
 */
public final class ReadersAfter {

    private ReadersAfter() {}

    public static List<CompositionBudget> theFigures(Held held) {
        return PublicationOrders.COMPOSITION_BUDGETS.keep(held.figures()).written();
    }

    public static List<NumericTerm> theTerms(Held held) {
        return new ArrayList<>(held.terms());
    }
}
