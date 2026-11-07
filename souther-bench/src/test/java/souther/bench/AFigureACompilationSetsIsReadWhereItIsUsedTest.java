package souther.bench;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Allowances;
import souther.compiler.partition.CompositionBudget;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A budget a compilation may hold to another figure ({@link Allowances#SETTABLE}) is asked for its
 * figure where the figure is used, and copied by no class into a constant of its own when the class
 * is loaded: a copy holds the figure declared for every compilation after, whatever one says.
 *
 * <p>Asked of the compiled code. A class whose initializer both reaches one of these budgets and
 * asks a budget for its figure is taken to copy it; the two together are what a copy compiles to,
 * and a class that reaches one to name it — in an order, or in the list of the settable ones —
 * asks no figure there.
 */
class AFigureACompilationSetsIsReadWhereItIsUsedTest {

    private static final String BUDGET = CompositionBudget.class.getName();

    @Test
    void noClassCopiesASettableFigureWhenItIsLoaded() {
        assertFalse(Allowances.SETTABLE.isEmpty(), "some budget may be set, or nothing is asked");
        Set<String> asksAFigureWhenLoaded = new TreeSet<>();
        Set<String> reachesASettableOneWhenLoaded = new TreeSet<>();
        Set<String> settable = new TreeSet<>();
        Allowances.SETTABLE.forEach(each -> settable.add(each.name()));
        for (Compiled.Site site : Compiled.sites()) {
            if (!site.method().equals("<clinit>") || !site.owner().equals(BUDGET)
                    || site.from().equals(BUDGET)) {
                continue;
            }
            if (site.how() == Compiled.How.CALLS && site.member().equals("maximum")) {
                asksAFigureWhenLoaded.add(site.from());
            }
            if (site.how() == Compiled.How.READS && settable.contains(site.member())) {
                reachesASettableOneWhenLoaded.add(site.from());
            }
        }
        assertFalse(asksAFigureWhenLoaded.isEmpty(),
                "some class copies a figure when it is loaded, or this reads no initializer");
        reachesASettableOneWhenLoaded.retainAll(asksAFigureWhenLoaded);
        assertEquals(List.of(), List.copyOf(reachesASettableOneWhenLoaded),
                "these copy a figure a compilation may set when they are loaded, and would hold"
                        + " the declared one whatever a compilation said");
    }
}
