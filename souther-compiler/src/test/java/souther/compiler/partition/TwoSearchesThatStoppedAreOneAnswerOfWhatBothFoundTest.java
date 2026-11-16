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
 * whichever came after it.
 */
class TwoSearchesThatStoppedAreOneAnswerOfWhatBothFoundTest {

    private static final Figure READINGS = WorkFigure.READINGS_OF_A_COMBINATION_TRIED.at(3);

    private static final Figure RUNS = WorkFigure.RUNS_FOR_ONE_READING.at(3);

    private static SearchShortfall met(CompositionBudget figure) {
        return SearchShortfall.of(CompositionShortfall.of(Set.of(figure)));
    }

    @Test
    void theFiguresEitherMetAreBothMet() {
        SearchStops first = new SearchStops(met(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                List.of(), false, Set.of());
        SearchStops second = new SearchStops(met(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                List.of(), false, Set.of());

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG,
                        CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                Set.copyOf(first.and(second).found().met().figures()));
        assertEquals(Set.copyOf(first.and(second).found().met().figures()),
                Set.copyOf(second.and(first).found().met().figures()));
    }

    @Test
    void theBoundsEitherStoppedAtAreBothKept() {
        SearchStops first = new SearchStops(SearchShortfall.NONE, List.of(READINGS), false,
                Set.of());
        SearchStops second = new SearchStops(SearchShortfall.NONE, List.of(RUNS), false,
                Set.of());

        assertEquals(Figure.inOrder(List.of(READINGS, RUNS)), first.and(second).boundsReached());
        assertEquals(first.and(second).boundsReached(), second.and(first).boundsReached());
    }

    @Test
    void aRunNothingWatchedInEitherIsOne() {
        SearchStops watched = new SearchStops(SearchShortfall.NONE, List.of(), false, Set.of());
        SearchStops unwatched = new SearchStops(SearchShortfall.NONE, List.of(), true, Set.of());

        assertTrue(watched.and(unwatched).metARunNothingWatched());
        assertTrue(unwatched.and(watched).metARunNothingWatched());
        assertFalse(watched.and(watched).metARunNothingWatched());
    }

    @Test
    void thePlanEitherWasCutShortIsCutShort() {
        SearchStops first = new SearchStops(SearchShortfall.NONE, List.of(), false,
                Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));
        SearchStops second = new SearchStops(SearchShortfall.NONE, List.of(), false, Set.of());

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                first.and(second).planCut());
        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG),
                second.and(first).planCut());
    }

    /** What was cut from the plan is not what the search met, and neither stands in for the
     *  other. */
    @Test
    void aFigureMetAndAFigureCutFromThePlanStayApart() {
        SearchStops met = new SearchStops(met(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                List.of(), false, Set.of());
        SearchStops cut = new SearchStops(SearchShortfall.NONE, List.of(), false,
                Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));

        SearchStops both = met.and(cut);

        assertEquals(List.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                List.copyOf(both.found().met().figures()));
        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG), both.planCut());
    }
}
