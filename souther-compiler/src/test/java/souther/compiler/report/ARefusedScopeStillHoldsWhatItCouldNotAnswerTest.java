package souther.compiler.report;

import souther.compiler.conformance.RepositoryModels;
import souther.compiler.query.Compilation;
import souther.test.ClosedWorldContract;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

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

    private record Scope(String name, AdequacyReport report) {}

    private static final List<Scope> SCOPES = everyScope();

    private static List<Scope> everyScope() {
        List<Scope> out = new ArrayList<>();
        for (Compilation compilation : RepositoryModels.all()) {
            AdequacyReport whole = AdequacyReport.of(compilation);
            out.add(new Scope(String.valueOf(compilation.modules()), whole));
            for (AdequacyReport.ModuleReport module : whole.modules()) {
                out.add(new Scope(module.module(), whole.only(module.module(), null)));
                for (AdequacyReport.BehaviorReport behavior : module.behaviors()) {
                    out.add(new Scope(module.module() + "/" + behavior.name(),
                            whole.only(module.module(), behavior.name())));
                }
            }
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
        List<Scope> refusedAndUnanswered = SCOPES.stream()
                .filter(each -> each.report().adequacy()
                        == AdequacyReport.AdequacyStatus.NOT_SATISFIED)
                .filter(each -> !each.report().assessment().uncertainties().isEmpty())
                .toList();

        assertFalse(refusedAndUnanswered.isEmpty(), "no model here is refused at a scope that also"
                + " went without something, which is the case this is a law about");
        for (Scope each : refusedAndUnanswered) {
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
        for (Scope each : SCOPES) {
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
     * <p>Narrowing selects and never works the entries out again: an entry a narrowed report holds
     * is one the whole report holds, and an entry of the whole is held by whichever scope owns its
     * subject. Only the first half is asked here — which subject belongs to which selection is the
     * selection's answer and is not written down anywhere to hold this against.
     */
    @Test
    void narrowingInventsNothing() {
        for (Compilation compilation : RepositoryModels.all()) {
            AdequacyReport whole = AdequacyReport.of(compilation);
            List<AdequacyUncertainty> ofTheWhole = whole.assessment().uncertainties();
            for (AdequacyReport.ModuleReport module : whole.modules()) {
                for (AdequacyUncertainty each
                        : whole.only(module.module(), null).assessment().uncertainties()) {

                    assertTrue(ofTheWhole.contains(each),
                            () -> module.module() + " holds " + each + " and the report it was"
                                    + " narrowed from does not");
                }
            }
        }
    }
}
