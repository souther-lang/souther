package souther.bench.readings.orders;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.publish.PublicationOrders;

import java.util.List;

/**
 * Two readers of a copy, each of which puts what it reads in an order.
 *
 * <p>Beside {@link ReadersAfter}, which has as many readers of the same copy and is not written
 * like this. What a check that counted the readers would say of the two is the same, and what one
 * that reads them would say is not.
 */
public final class ReadersBefore {

    private ReadersBefore() {}

    public static List<CompositionBudget> theFigures(Held held) {
        return PublicationOrders.COMPOSITION_BUDGETS.keep(held.figures()).written();
    }

    public static List<NumericTerm> theTerms(Held held) {
        return NumericTerms.inOrder(held.terms());
    }
}
