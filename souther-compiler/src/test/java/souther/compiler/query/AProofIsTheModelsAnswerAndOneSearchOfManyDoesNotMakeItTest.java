package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.Generator;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.publish.PublicationOrders;

import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A point the rules leave no value at is answered rather than open, and it takes every search of
 * the point to say so.
 *
 * <p>Two things are held here and they are one rule read at two sizes. What one search comes back
 * with may be the model's own word — the rules on the way to the point leave it nothing — and that
 * is not one of the ways this compiler falls short, so it may not arrive as the state for a point
 * nothing was shown about. And a point is searched once per way of standing the dependencies in, so
 * a word that settles one of those settles the region that search was composed in and not the
 * point: what the point comes to is what all of them came to.
 *
 * <p>Put to the fold directly. What varies is the outcomes of one point, which no pair of models
 * varies on its own — a model that puts two searches at one point differs in the way to it as well,
 * and the comparison would be about the difference rather than about the quantifier.
 */
class AProofIsTheModelsAnswerAndOneSearchOfManyDoesNotMakeItTest {

    private static final WayToTheBorder WAY = new WayToTheBorder(List.of());

    /** One search that proves the rules leave nothing at the point. */
    @Test
    void oneSearchThatProvesItIsTheModelsAnswer() {
        assertEquals(new WritabilityKnowledge.Refuted(), knowledge(SearchOutcomes.of(proof())),
                "the rules leaving no value at the point is what the search came back with, and it"
                        + " is not a showing nobody made");
    }

    /** And two of them, which is the point being searched under two callers and answered by both. */
    @Test
    void everySearchProvingItIsStillTheModelsAnswer() {
        assertEquals(new WritabilityKnowledge.Refuted(),
                knowledge(SearchOutcomes.of(proof()).plus(SearchOutcomes.of(proof()))),
                "two ways of standing the dependencies in, and the rules leave nothing under"
                        + " either");
    }

    /**
     * A proof beside a search a budget ended is not the point's answer.
     *
     * <p>What the proof is about is the region that search was composed in, and the other search
     * was composed in another. Read as the point's, this compiler would be saying no row can be
     * written at a point it stopped looking for one at — which is a figure of its own reported as
     * the model's word.
     */
    @Test
    void aProofBesideASearchThatWasStoppedIsNotTheAnswer() {
        WritabilityKnowledge knowledge =
                knowledge(SearchOutcomes.of(proof()).plus(SearchOutcomes.of(stopped())));

        assertEquals(WritabilityKnowledge.Prevented.by(EstablishmentGap.Composition.of(
                        EnumSet.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS), List.of())),
                knowledge,
                "one search proved its own region empty and the other was stopped, so what the"
                        + " point is owed is the figure that would have to give");
    }

    /**
     * And a proof beside a search nobody could make is not the answer either.
     *
     * <p>A search that never ran proves nothing and stops nothing, so the point is left with a
     * proof about one region and no word about the other — which is the state for a point nothing
     * has shown anything about.
     */
    @Test
    void aProofBesideASearchNobodyCouldMakeIsNotTheAnswer() {
        assertEquals(new WritabilityKnowledge.NoEvidence(),
                knowledge(SearchOutcomes.of(proof()).plus(SearchOutcomes.of(
                        new ItemAssessment.Attempt.Unavailable(
                                ItemAssessment.Attempt.Reason.NO_CLASSES)))),
                "nothing was searched under the second caller, so nothing is known about it");
    }

    /** A word that says what this compiler did not manage is not a proof, however it reads. */
    @Test
    void awordAboutThisCompilerIsNotAProof() {
        assertEquals(new WritabilityKnowledge.NoEvidence(),
                knowledge(SearchOutcomes.of(came(
                        Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED))),
                "every candidate refused says nothing about the ones that were not tried");
    }

    /** And a point nobody searched is not a point the rules refuse. */
    @Test
    void aPointNobodySearchedIsNotAProof() {
        assertEquals(new WritabilityKnowledge.NoEvidence(), knowledge(SearchOutcomes.none()),
                "a universal over no searches is not the rules having answered");
    }

    /**
     * What the account does with the proof: the obligation stands and is answered.
     *
     * <p>Both of the coverages a proved point arrives with, because the readings do not bear on it.
     * A point no value can be at has no row at it whether every row was read against it or none
     * was, so the state is the same and neither of the two questions is open.
     */
    @Test
    void theObligationStandsAndIsAnswered() {
        assertEquals(new ObligationDisposition.Refuted(),
                ObligationDisposition.of(new ObligationCoverage.Missed(),
                        new WritabilityKnowledge.Refuted()),
                "the rows ran out and no row can be written there, which is answered and not open");
        assertEquals(new ObligationDisposition.Refuted(),
                ObligationDisposition.of(
                        new ObligationCoverage.NotMeasured(
                                UnaskedReasons.of(ItemAssessment.Coverage.NotAsked.NO_ROWS)),
                        new WritabilityKnowledge.Refuted()),
                "nobody wrote a row for the behavior, and reading one would not put a value where"
                        + " the rules leave none");
    }

    private static WritabilityKnowledge knowledge(SearchOutcomes searches) {
        return WritabilityKnowledge.of(
                ItemAssessment.WritabilityEvidence.of(List.of()), searches);
    }

    private static ItemAssessment.Attempt proof() {
        return came(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE);
    }

    private static ItemAssessment.Attempt came(Generator.UnresolvedCombination.Reason to) {
        return new ItemAssessment.Attempt.Unresolved(
                new Generator.UnresolvedCombination(List.of("p.x = 11"), to), WAY);
    }

    private static ItemAssessment.Attempt stopped() {
        CompositionBudget budget = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS;
        return new ItemAssessment.Attempt.Stopped(
                new Generator.UnresolvedCombination(List.of("p.x = 11"),
                        Generator.UnresolvedCombination.Reason.wordFor(Set.of(budget))),
                WAY, souther.compiler.partition.CompositionAccount.NOTHING,
                PublicationOrders.COMPOSITION_BUDGETS.keep(EnumSet.of(budget)),
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(List.of()));
    }
}
