package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A run of a plan a figure left unmade ({@link FillResult#leftAt}) says the figure at a
 * replacement as it does at every other obligation: in the words a search for a rewrite says one
 * in, with the figure as it stood, and not as a search that composed nothing.
 */
class ARunAFigureLeftUnmadeSaysTheFigureAtAReplacementTest {

    @Test
    void aFigureIsSaidAsAFigureOfTheComposing() {
        CompositionBudget figure = CompositionBudget.SEARCHES_A_ROW_IS_COMPOSED_THROUGH;
        assertEquals(new ReplacementDisposition.NoneFound(Map.of(
                        ReplacementDisposition.Ended.A_FIGURE_OF_THE_COMPOSING,
                        ReplacementDisposition.Met.at(Set.of(figure.figure())))),
                FillResult.noneComposed(CompositionShortfall.of(Set.of(figure))));
    }

    @Test
    void nothingMetIsNothingComposed() {
        assertEquals(new ReplacementDisposition.NoneFound(
                        ReplacementDisposition.Ended.NOTHING_WAS_COMPOSED),
                FillResult.noneComposed(CompositionShortfall.NONE));
    }
}
