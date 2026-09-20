package souther.compiler.report;

import souther.compiler.conformance.RepositoryModels;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.test.ClosedWorldContract;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Narrowing a report chooses which of a module's declaration debts a reader is shown, and says of
 * each one it shows what the module says.
 *
 * <p>A line an {@code invariant} drew is not any behavior's. It is owed once wherever the type is
 * carried and a row written for any behavior carrying it meets it, so what became of the debt is
 * the module's answer and what showed a row can be written at its points is the module's readings.
 * Which behaviors a reader is shown decides which of those debts are work that reader can do; it
 * decides nothing about what became of the ones that are.
 *
 * <p><b>Both halves, and they narrow differently.</b> A selection that kept every debt would show a
 * reader work nobody on the page can do, and one that answered a kept debt again from the rows of
 * the behaviors it shows would answer it from strictly less than the module answered it from — and
 * report a point nothing showed a row for at a line the module has a row for.
 *
 * <p><b>Over the models this repository carries.</b> Whether a debt survives narrowing while some
 * of its readings do not is the corpus's answer: built by hand, this would hold a value against
 * itself.
 */
@ClosedWorldContract
class ANarrowedReportAnswersItsDeclarationDebtsFromTheModuleTest {

    /**
     * One repository model's report, beside every report a reader of it can be handed.
     *
     * <p>Kept together because a debt is compared with the one the report it was narrowed from
     * holds, and a module name is only a name: two models naming a module alike would otherwise be
     * held against each other.
     *
     * @param whole the report every scope beside it was narrowed from
     * @param scopes every scope of it, {@link ReportScopes}'s and not walked here
     */
    private record OfAModel(AdequacyReport whole, List<ReportScopes> scopes) {

        static List<OfAModel> all() {
            List<OfAModel> out = new ArrayList<>();
            for (Compilation compilation : RepositoryModels.all()) {
                AdequacyReport whole = AdequacyReport.of(compilation);
                out.add(new OfAModel(whole, ReportScopes.of(
                        String.valueOf(compilation.modules()), whole)));
            }
            return List.copyOf(out);
        }
    }

    private static final List<OfAModel> MODELS = OfAModel.all();

    /**
     * A debt a narrowed report shows is the debt the whole report shows, answer and all.
     *
     * <p>Held as equality of the debt itself rather than of the word a page writes for it. What a
     * debt came to is a value, and a selection that changed any part of it — what it asks of a row,
     * what became of it, which readings settled it — changed the module's answer.
     */
    @Test
    void aDebtANarrowedReportShowsIsTheOneTheWholeReportShows() {
        List<BorderObligationPoint> compared = new ArrayList<>();
        for (OfAModel model : MODELS) {
            for (ReportScopes scope : model.scopes()) {
                for (AdequacyReport.ModuleReport module : scope.report().modules()) {
                    Map<BorderObligationPoint, Adequacy.DeclaredDebt> whole =
                            debtsOf(moduleOf(model.whole(), module.module()));
                    for (Adequacy.DeclaredDebt each : debtsOf(module).values()) {
                        compared.add(each.debt().point());

                        assertEquals(whole.get(each.debt().point()), each,
                                () -> scope.name() + " shows a debt of " + module.module()
                                        + " the whole report does not show that way: "
                                        + each.debt().point());
                    }
                }
            }
        }

        assertFalse(compared.isEmpty(), "no model here narrows to a report that shows a declaration"
                + " debt, which is the case this is a law about");
    }

    /**
     * And narrowing does drop debts, so the law above is not held over every debt there is.
     *
     * <p>The control. Were every debt carried by every behavior, a selection that kept all of them
     * would satisfy the law and nothing here would say it had chosen anything.
     */
    @Test
    void narrowingShowsFewerDebtsThanTheModuleHolds() {
        List<String> narrowed = new ArrayList<>();
        for (OfAModel model : MODELS) {
            for (ReportScopes scope : model.scopes()) {
                for (AdequacyReport.ModuleReport module : scope.report().modules()) {
                    if (debtsOf(module).size()
                            < debtsOf(moduleOf(model.whole(), module.module())).size()) {
                        narrowed.add(scope.name());
                    }
                }
            }
        }

        assertFalse(narrowed.isEmpty(), "no selection of these models leaves out a declaration"
                + " debt, so the law beside this one is held over nothing that was chosen");
    }

    private static AdequacyReport.ModuleReport moduleOf(AdequacyReport report, String module) {
        return report.modules().stream()
                .filter(each -> each.module().equals(module))
                .findFirst().orElse(null);
    }

    private static Map<BorderObligationPoint, Adequacy.DeclaredDebt> debtsOf(
            AdequacyReport.ModuleReport module) {
        if (module == null || module.owedByDeclarations().owed() == null) {
            return Map.of();
        }
        Map<BorderObligationPoint, Adequacy.DeclaredDebt> out = new LinkedHashMap<>();
        for (Adequacy.DeclaredDebt each : module.owedByDeclarations().owed().owed()) {
            out.put(each.debt().point(), each);
        }
        return out;
    }
}
