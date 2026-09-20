package souther.compiler.report;

import souther.compiler.conformance.RepositoryModels;
import souther.compiler.query.Compilation;
import souther.test.ClosedWorldContract;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a scope could not answer is there whether or not its verdict shows it.
 *
 * <p>Three things this report used to answer with one. What the measures came to is the analysis's;
 * which of it settles a word is a ranking over that; what a reader of the verdict is shown is the
 * ranking's answer. A gap outranks, so a refused scope shows nothing that holds it open — and the
 * things it could not answer are no less there for being outranked.
 *
 * <p>Held over every scope a report can be narrowed to, because the ranking is per scope and a
 * module's gap is not its sibling's. A module whose bodies were never made sits beside one the rows
 * refuse, and read through the compilation's verdict alone it looks like a module short of nothing.
 *
 * <p><b>Over the models this repository carries.</b> Whether a refused scope that still holds
 * something unanswered exists at all is the corpus's answer and not a value a test can build — built
 * by hand, this would say a record can be constructed, which javac already says.
 */
@ClosedWorldContract
class ARefusedScopeStillHoldsWhatItCouldNotAnswerTest {

    /**
     * Every report a reader of these models can be handed.
     *
     * <p>{@link ReportScopes}'s and not walked here, because the other law over these is held over
     * the same population and two enumerations of it drift.
     */
    private static final List<ReportScopes> SCOPES = everyScope();

    private static List<ReportScopes> everyScope() {
        List<ReportScopes> out = new ArrayList<>();
        for (Compilation compilation : RepositoryModels.all()) {
            out.addAll(ReportScopes.of(String.valueOf(compilation.modules()),
                    AdequacyReport.of(compilation)));
        }
        return List.copyOf(out);
    }

    /**
     * A scope the rows refuse holds what it could not answer, and shows a reader none of it.
     *
     * <p>Both halves. The first is what the assessment is for and the second is what the verdict
     * means, and a change that collapses them again satisfies one of these and not the other.
     */
    @Test
    void aRefusedScopeKeepsItsUncertaintiesAndOffersNone() {
        List<ReportScopes> refusedAndUnanswered = SCOPES.stream()
                .filter(each -> each.report().adequacy()
                        == AdequacyReport.AdequacyStatus.NOT_SATISFIED)
                .filter(each -> !each.report().assessment().uncertainties().isEmpty())
                .toList();

        assertFalse(refusedAndUnanswered.isEmpty(), "no model here is refused at a scope that also"
                + " went without something, which is the case this is a law about");
        for (ReportScopes each :refusedAndUnanswered) {
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
        for (ReportScopes each :SCOPES) {
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
        for (Compilation compilation : RepositoryModels.all()) {
            AdequacyReport whole = AdequacyReport.of(compilation);
            Set<AdequacyUncertainty> ofTheWhole =
                    new HashSet<>(whole.assessment().uncertainties());
            for (ReportScopes scope : ReportScopes.of(
                    String.valueOf(compilation.modules()), whole)) {
                for (AdequacyUncertainty each : scope.report().assessment().uncertainties()) {

                    assertTrue(ofTheWhole.contains(each),
                            () -> scope.name() + " holds " + each + " and the report it was"
                                    + " narrowed from does not");
                }
            }
        }
    }
}
