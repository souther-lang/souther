package souther.bench;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Allowances;
import souther.compiler.partition.CompositionBudget;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    /**
     * What a budget is asked where it is read off at once and not handed on: a figure, or its
     * place among the budgets, which is what a switch over them compiles to.
     */
    private static final Set<String> READ_OFF = Set.of("reached", "maximum", "declared",
            "ordinal");

    /**
     * The places that name a budget a compilation may set and hand on the budget itself, and why
     * none of them is a stop that would be told by the budget: each names it as one of the
     * budgets, not as something stopped at it.
     */
    private static final Map<String, String> NAMED_AS_A_BUDGET = Map.of(
            "souther.compiler.partition.Allowances#<clinit>()V",
            "the budgets a compilation may set, which this rule is about",
            "souther.compiler.publish.PublicationOrders#<clinit>()V",
            "the order the budgets are written out in");

    /**
     * A budget a compilation may set is read off where it is named: the figure it stopped at
     * ({@link CompositionBudget#reached}) or the figure it is held to, never the budget handed on
     * by itself. A stop that holds a budget by its kind and makes the figure when it is told says
     * the one in force then, which outside a compilation is the one declared; so a budget that may
     * be set reaches no such holder, whichever of them it is, because nothing hands it on.
     *
     * <p>Asked of the compiled code, where naming a budget is reading its constant, and what is
     * done with it is the next instruction. A place that hands it on as one of the budgets — an
     * order, the list of the settable ones — says so here, and is no stop.
     */
    @Test
    void aBudgetACompilationMaySetIsReadOffWhereItIsNamed() {
        Set<String> settable = new TreeSet<>();
        Allowances.SETTABLE.forEach(each -> settable.add(each.name()));
        Set<String> handedOn = new TreeSet<>();
        int readOff = 0;
        for (Compiled.StaticRead each : Compiled.staticReads()) {
            Compiled.Site read = each.read();
            if (!read.owner().equals(BUDGET) || !settable.contains(read.member())
                    || read.from().equals(BUDGET)) {
                continue;
            }
            Compiled.Site taken = each.takenBy();
            if (taken != null && taken.owner().equals(BUDGET)
                    && READ_OFF.contains(taken.member())) {
                readOff++;
            } else {
                handedOn.add(read.at());
            }
        }
        assertTrue(readOff > 0, "some place reads a settable budget's figure, or nothing is read");
        Set<String> unsaid = new TreeSet<>(handedOn);
        unsaid.removeAll(NAMED_AS_A_BUDGET.keySet());
        assertEquals(List.of(), List.copyOf(unsaid),
                "these hand on a budget a compilation may set by itself, where a holder of the"
                        + " budget would tell the figure in force when it is read");
        Set<String> gone = new TreeSet<>(NAMED_AS_A_BUDGET.keySet());
        gone.removeAll(handedOn);
        assertEquals(List.of(), List.copyOf(gone), "these no longer name one");
    }
}
