package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.observe.Figure;
import souther.compiler.observe.WorkFigure;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A search looked for again, or along several ways, answers once, and what each of them found out
 * and was stopped by is in the answer: a figure one of them met is a number somebody can raise
 * whichever came after it. Each test has the earlier search carry what is asked after, and the
 * later one carry nothing, so that taking the last would lose it.
 */
class TwoSearchesThatStoppedAreOneAnswerOfWhatBothFoundTest {

    private static final Figure READINGS = WorkFigure.READINGS_OF_A_COMBINATION_TRIED.at(3);

    private static final SearchStops NOTHING =
            new SearchStops(SearchShortfall.NONE, List.of(), false, Set.of());

    private static SearchStops with(SearchShortfall found, List<Figure> bounds, boolean unwatched,
                                    Set<CompositionBudget> cut) {
        return new SearchStops(found, bounds, unwatched, cut);
    }

    @Test
    void theFiguresTheEarlierMetAreMet() {
        SearchShortfall met = SearchShortfall.of(
                CompositionShortfall.of(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG)));

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG), Set.copyOf(
                with(met, List.of(), false, Set.of()).and(NOTHING).found().met().figures()));
    }

    @Test
    void theBoundsTheEarlierStoppedAtAreKept() {
        assertEquals(List.of(READINGS),
                with(SearchShortfall.NONE, List.of(READINGS), false, Set.of()).and(NOTHING)
                        .boundsReached());
    }

    @Test
    void aRunNothingWatchedInTheEarlierIsOne() {
        assertTrue(with(SearchShortfall.NONE, List.of(), true, Set.of()).and(NOTHING)
                .metARunNothingWatched());
        assertFalse(NOTHING.and(NOTHING).metARunNothingWatched());
    }

    /** What was cut from the plan is not what the search met, and neither stands in for the
     *  other. */
    @Test
    void thePlanTheEarlierWasCutShortIsCutShortApartFromWhatWasMet() {
        SearchShortfall met = SearchShortfall.of(
                CompositionShortfall.of(Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT)));

        SearchStops both = with(SearchShortfall.NONE, List.of(), false,
                Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG))
                .and(with(met, List.of(), false, Set.of()));

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG), both.planCut());
        assertEquals(List.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                List.copyOf(both.found().met().figures()));
    }
}
