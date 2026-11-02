package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.Generator;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.publish.PublicationOrders;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What a second stage of a search was short of joins what the first came to, whichever shape the
 * first came to in. Each outcome carries what it was short of in its own shape, and a stage that
 * only knew one of them lost its shortfall on every other, without a word.
 */
class AnOutcomeIsShortOfWhatASecondStageWasShortOfWhateverShapeItIsInTest {

    private static final CompositionBudget EARLIER = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS;

    private static final CompositionBudget LATER =
            CompositionBudget.ROWS_BESIDE_A_RUN_ARE_MADE_FOR_A_POINT;

    private static final CompositionRepertoire WALKED =
            CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_SIZES;

    private static final CompositionRepertoire ALSO_WALKED =
            CompositionRepertoire.MAPS_WRITTEN_WITH_ONE_ENTRY;

    private static Generator.UnresolvedCombination said(
            Generator.UnresolvedCombination.Reason reason) {
        return new Generator.UnresolvedCombination(List.of("p"), reason);
    }

    private static final Generator.UnresolvedCombination NOT_FOUND =
            said(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS);

    private static ItemAssessment.Attempt.Unexhausted walkedSomeOf(CompositionRepertoire... these) {
        return new ItemAssessment.Attempt.Unexhausted(NOT_FOUND, WayToTheBorder.UNTOUCHED,
                CompositionAccount.NOTHING,
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of(these)),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(Set.of()));
    }

    private static ItemAssessment.Attempt.Limited limitedBy(CompositionBudget figure) {
        return new ItemAssessment.Attempt.Limited(NOT_FOUND, WayToTheBorder.UNTOUCHED,
                CompositionAccount.NOTHING,
                PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of(figure)),
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of(WALKED)),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(Set.of()));
    }

    private static ItemAssessment.Attempt.Stopped stoppedBy(CompositionBudget figure) {
        return new ItemAssessment.Attempt.Stopped(
                said(Generator.UnresolvedCombination.Reason.wordFor(Set.of(figure))),
                WayToTheBorder.UNTOUCHED, CompositionAccount.NOTHING,
                PublicationOrders.COMPOSITION_BUDGETS.keep(Set.of(figure)),
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(Set.of()),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(Set.of()));
    }

    private static CompositionShortfall figure(CompositionBudget figure) {
        return CompositionShortfall.of(Set.of(figure));
    }

    /** The case that was lost: the first stage walked some of a population, the second ran out. */
    @Test
    void anOutcomeThatWalkedSomeOfAPopulationIsAlsoLimitedByTheLaterFigure() {
        ItemAssessment.Attempt now = ItemAssessment.Attempt.alsoShortOf(walkedSomeOf(WALKED),
                figure(LATER));

        ItemAssessment.Attempt.Limited limited = (ItemAssessment.Attempt.Limited) now;
        assertEquals(List.of(LATER), limited.limitedBy().written());
        assertEquals(List.of(WALKED), limited.notAllOf().written());
    }

    /** One that was limited keeps its figure, and has the later one beside it. */
    @Test
    void anOutcomeAlreadyLimitedKeepsItsFigureAndHasTheLaterOne() {
        ItemAssessment.Attempt.Limited now = (ItemAssessment.Attempt.Limited)
                ItemAssessment.Attempt.alsoShortOf(limitedBy(EARLIER), figure(LATER));

        assertEquals(Set.of(EARLIER, LATER), Set.copyOf(now.limitedBy().written()));
        assertEquals(List.of(WALKED), now.notAllOf().written());
    }

    /** A stop by one figure is a stop by both, and the word it comes back with agrees. */
    @Test
    void anOutcomeAStopCameToIsStoppedByBothAndSaysAWordThatAgrees() {
        ItemAssessment.Attempt.Stopped now = (ItemAssessment.Attempt.Stopped)
                ItemAssessment.Attempt.alsoShortOf(stoppedBy(EARLIER), figure(LATER));

        assertEquals(Set.of(EARLIER, LATER), Set.copyOf(now.stoppedBy().written()));
        assertEquals(Generator.UnresolvedCombination.Reason.wordFor(Set.of(EARLIER, LATER)),
                now.why().reason());
    }

    /** One that came to nothing is limited if a figure is why, and walked some of it if not. */
    @Test
    void anOutcomeThatCameToNothingWearsWhatWasShortOfInItsOwnVocabulary() {
        ItemAssessment.Attempt.Unresolved none = new ItemAssessment.Attempt.Unresolved(NOT_FOUND,
                WayToTheBorder.UNTOUCHED);

        ItemAssessment.Attempt.Limited byFigure = (ItemAssessment.Attempt.Limited)
                ItemAssessment.Attempt.alsoShortOf(none, figure(LATER));
        ItemAssessment.Attempt.Unexhausted byPopulation = (ItemAssessment.Attempt.Unexhausted)
                ItemAssessment.Attempt.alsoShortOf(none, CompositionShortfall.writing(Set.of(WALKED)));

        assertEquals(List.of(LATER), byFigure.limitedBy().written());
        assertEquals(List.of(WALKED), byPopulation.notAllOf().written());
    }

    /** A population joins the populations, and no figure appears that nothing reached. */
    @Test
    void aPopulationJoinsThePopulationsAndMakesNoFigure() {
        ItemAssessment.Attempt now = ItemAssessment.Attempt.alsoShortOf(walkedSomeOf(WALKED),
                CompositionShortfall.writing(Set.of(ALSO_WALKED)));

        ItemAssessment.Attempt.Unexhausted walked = (ItemAssessment.Attempt.Unexhausted) now;
        assertEquals(Set.of(WALKED, ALSO_WALKED), Set.copyOf(walked.notAllOf().written()));
    }

    /** Nothing short, and an outcome that was not a search, are as they were. */
    @Test
    void nothingShortAndWhatWasNotSearchedAreAsTheyWere() {
        ItemAssessment.Attempt walked = walkedSomeOf(WALKED);
        ItemAssessment.Attempt unavailable = new ItemAssessment.Attempt.Unavailable(
                ItemAssessment.Attempt.Reason.NO_CLASSES);

        assertSame(walked, ItemAssessment.Attempt.alsoShortOf(walked, CompositionShortfall.NONE));
        assertSame(unavailable, ItemAssessment.Attempt.alsoShortOf(unavailable, figure(LATER)));
    }
}
