package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.Generator;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.publish.PublicationOrders;

import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point whose search wrote some of a population that is of the number and not of the value is
 * short of it at every value, so a point is not asked for a second value once every search at the
 * first came back short of one.
 *
 * <p>Only then. A search short of a population one value admits — the ways a total is spread over
 * the elements, say — may be short of none at another, and a search that came to anything else may
 * come to a row.
 */
class AShortfallOfTheNumberIsAShortfallAtEveryValueTest {

    private static final Generator.UnresolvedCombination WHY = new Generator.UnresolvedCombination(
            List.of("List.sum(p.xs) = 7"),
            Generator.UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED);

    private static final WayToTheBorder WAY = new WayToTheBorder(List.of());

    /** A computed total nothing solves for is written short of at every value; the ways a total
     *  is spread are not. */
    @Test
    void onlyAPopulationOfTheNumberIsMetWhateverTheValue() {
        assertTrue(CompositionRepertoire.ELEMENTS_A_COMPUTED_TOTAL_IS_SOLVED_FOR
                .metWhateverTheValue());
        assertFalse(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD.metWhateverTheValue());
    }

    @Test
    void aSearchShortOfAPopulationOfTheNumberIsShortAtEveryValue() {
        assertTrue(SearchOutcomes.of(unexhausted(
                CompositionRepertoire.ELEMENTS_A_COMPUTED_TOTAL_IS_SOLVED_FOR))
                .shortWhateverTheValue());
    }

    /** A figure met beside it leaves the row unwritten at any value all the same. */
    @Test
    void aFigureMetBesideItChangesNothing() {
        assertTrue(SearchOutcomes.of(limited(
                CompositionRepertoire.ELEMENTS_A_COMPUTED_TOTAL_IS_SOLVED_FOR))
                .shortWhateverTheValue());
    }

    @Test
    void aSearchShortOfWhatOneValueAdmitsIsNot() {
        assertFalse(SearchOutcomes.of(unexhausted(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD))
                .shortWhateverTheValue());
    }

    /** Every search at the point, and not one of them: another way of standing the dependencies
     *  in that came to something else may come to a row at another value. */
    @Test
    void everySearchAtThePointIsShortOrNoneIs() {
        SearchOutcomes both = SearchOutcomes.of(unexhausted(
                CompositionRepertoire.ELEMENTS_A_COMPUTED_TOTAL_IS_SOLVED_FOR))
                .plus(SearchOutcomes.of(new ItemAssessment.Attempt.Unresolved(new
                        Generator.UnresolvedCombination(List.of("p.x = 11"),
                        Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED), WAY)));
        assertFalse(both.shortWhateverTheValue());
    }

    /** No search is no shortfall. */
    @Test
    void noSearchIsNoShortfall() {
        assertFalse(SearchOutcomes.none().shortWhateverTheValue());
    }

    private static ItemAssessment.Attempt unexhausted(CompositionRepertoire notAllOf) {
        return new ItemAssessment.Attempt.Unexhausted(WHY, WAY, CompositionAccount.NOTHING,
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(EnumSet.of(notAllOf)),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(List.of()));
    }

    private static ItemAssessment.Attempt limited(CompositionRepertoire notAllOf) {
        return new ItemAssessment.Attempt.Limited(WHY, WAY, CompositionAccount.NOTHING,
                PublicationOrders.COMPOSITION_BUDGETS.keep(
                        Set.of(CompositionBudget.DEPTH_A_CONSTRUCTION_PLAN_DESCENDS)),
                PublicationOrders.COMPOSITION_REPERTOIRES.keep(EnumSet.of(notAllOf)),
                PublicationOrders.COMPOSITION_CAPACITIES.keep(List.of()));
    }
}
