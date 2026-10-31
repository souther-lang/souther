package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a scope could not answer is there whether or not its verdict shows it, and narrowing to one
 * never invents an answer the report it was narrowed from does not hold, on two models that each
 * raise one case of it: a rule the rows refuse beside a declaration that owes a row at a line, and
 * a value built that its own rule rejects.
 *
 * <p>Three things a report used to answer with one. What the measures came to is the analysis's;
 * which of it settles a word is a ranking over that; what a reader of the verdict is shown is the
 * ranking's answer. A gap outranks, so a refused scope shows nothing that holds it open — and the
 * things it could not answer are no less there for being outranked.
 *
 * <p>Held over every scope a report can be narrowed to, because the ranking is per scope and a
 * module's gap is not its sibling's.
 */
class AScopeOfAModelStillHoldsWhatItCouldNotAnswerTest {

    /** A limit on a weighted sum of two counts and one on the distance between two hours, each
     *  behavior taking types of its own: the rows refuse the scope and the declarations owe rows at
     *  the lines, which a scope narrowed to one behavior does not carry for the other. */
    private static final String LIMITS = """
            module limits exposing ( Straws, Bars, Load, Rejected, packBox, Hour, Booked, Clash,
                                     bookSlot )

            data Straws = Int
                invariant value >= 0 && value <= 20

            data Bars = Int
                invariant value >= 0 && value <= 20

            data Load = { grams: Int }
            data Rejected

            behavior packBox : (straws: Straws, bars: Bars) -> Load | Rejected
                constructs Load

            let packBox (straws, bars) = {
                guard 300 * straws.value + 600 * bars.value <= 4800 else Rejected
                Load { grams = 300 * straws.value + 600 * bars.value }
            }

            data Hour = Int
                invariant value >= 0 && value <= 24

            data Booked = { from: Hour, until: Hour }
            data Clash

            behavior bookSlot : (from: Hour, until: Hour) -> Booked | Clash
                constructs Booked

            let bookSlot (from, until) = {
                guard until.value - from.value <= 8 else Clash
                Booked { from = from, until = until }
            }
            """;

    /** A value built that its own rule rejects, which leaves the scope undetermined. */
    private static final String REJECTS = """
            module rejects exposing ( Hold, hold )

            data Hold = Int
                invariant value >= 1 && value <= 300

            behavior hold : (party: Int) -> Hold
                constructs Hold

            let hold (party) = Hold(0)
            """;

    /**
     * One model's report, beside every report a reader of it can be handed.
     *
     * <p>Kept together, because more than one law needs the narrowed reports beside the whole one
     * they came from — a debt a narrowed report shows is compared with the one the whole report
     * shows, and a module name is only a name: two models naming a module alike would otherwise be
     * held against each other.
     *
     * @param whole the report every scope beside it was narrowed from
     * @param scopes every scope of it, {@link ReportScopes}'s and not walked here
     */
    private record OfAModel(AdequacyReport whole, List<ReportScopes> scopes) {

        static OfAModel of(Compilation compilation) {
            AdequacyReport whole = AdequacyReport.of(compilation);
            return new OfAModel(whole, ReportScopes.of(String.valueOf(compilation.modules()),
                    whole));
        }
    }

    private static List<OfAModel> models() {
        return List.of(OfAModel.of(compiled(LIMITS)), OfAModel.of(compiled(REJECTS)));
    }

    private static List<ReportScopes> scopesOf(List<OfAModel> models) {
        return models.stream().flatMap(each -> each.scopes().stream()).toList();
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * A scope the rows refuse holds what it could not answer, and shows a reader none of it.
     *
     * <p>Both halves. The first is what the assessment is for and the second is what the verdict
     * means, and a change that collapses them again satisfies one of these and not the other.
     */
    @Test
    void aRefusedScopeKeepsItsUncertaintiesAndOffersNone() {
        List<ReportScopes> refusedAndUnanswered = scopesOf(models()).stream()
                .filter(each -> each.report().adequacy()
                        == AdequacyReport.AdequacyStatus.NOT_SATISFIED)
                .filter(each -> !each.report().assessment().uncertainties().isEmpty())
                .toList();

        assertFalse(refusedAndUnanswered.isEmpty(), "no model here is refused at a scope that also"
                + " went without something, which is the case this is a law about");
        for (ReportScopes each : refusedAndUnanswered) {
            assertTrue(each.report().whatKeepsTheVerdictOpen().isEmpty(),
                    () -> each.name() + " is refused and offers a reader something that holds its"
                            + " verdict open");
        }
    }

    /**
     * And where nothing is refused, what a reader is shown is the whole of what was not answered.
     *
     * <p>The other direction, which is what keeps the ranking from quietly dropping an entry on its
     * way to the page.
     */
    @Test
    void anUndeterminedScopeShowsEverythingItCouldNotAnswer() {
        for (ReportScopes each : scopesOf(models())) {
            if (each.report().adequacy() != AdequacyReport.AdequacyStatus.UNDETERMINED) {
                continue;
            }

            assertEquals(each.report().assessment().uncertainties(),
                    each.report().whatKeepsTheVerdictOpen(),
                    () -> each.name() + " is undetermined and shows a reader something other than"
                            + " what it could not answer");
        }
    }

    /**
     * What the analysis came to does not depend on where the reader is standing.
     *
     * <p>A report narrowed to a selection works its entries out again from the parts it kept, and
     * what is held is that doing so invents nothing: an entry it holds is one the whole report
     * holds. The other direction — that a selection keeps every entry belonging to it — is not
     * asked, because which subject belongs to which selection is the selection's answer and is
     * written down nowhere to hold it against.
     *
     * <p>Held at every grain a selection has. A behavior's rows are what showed a row can be
     * written at the points of a line an {@code invariant} drew, and a selection that answered such
     * a line again from the behaviors it shows would come back undecided at a point the module has
     * a row for — an entry of the narrowed report and of nothing it was narrowed from.
     */
    @Test
    void narrowingInventsNothing() {
        for (OfAModel model : models()) {
            Set<AdequacyUncertainty> ofTheWhole =
                    new HashSet<>(model.whole().assessment().uncertainties());
            for (ReportScopes scope : model.scopes()) {
                for (AdequacyUncertainty each : scope.report().assessment().uncertainties()) {

                    assertTrue(ofTheWhole.contains(each),
                            () -> scope.name() + " holds " + each + " and the report it was"
                                    + " narrowed from does not");
                }
            }
        }
    }

    /**
     * A debt a narrowed report shows is the debt the whole report shows, answer and all.
     *
     * <p>Held as equality of the debt itself rather than of the word a page writes for it. What a
     * debt came to is a value, and a selection that changed any part of it — what it asks of a row,
     * what became of it, which readings settled it — changed the module's answer.
     *
     * <p>Both halves, and they narrow differently: a selection that kept every debt would show a
     * reader work nobody on the page can do, and one that answered a kept debt again from the rows
     * of the behaviors it shows would answer it from strictly less than the module answered it
     * from — and report a point nothing showed a row for at a line the module has a row for.
     */
    @Test
    void aDebtANarrowedReportShowsIsTheOneTheWholeReportShows() {
        List<BorderObligationPoint> compared = new ArrayList<>();
        for (OfAModel model : models()) {
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
        for (OfAModel model : models()) {
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
