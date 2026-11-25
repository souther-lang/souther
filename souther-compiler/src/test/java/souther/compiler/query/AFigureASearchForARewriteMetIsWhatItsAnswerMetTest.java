package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ReplacementDisposition;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A search for a rewrite that ended at a figure of the composing is told as one that met that
 * figure: the number an author raises, in the figure's word, and not a search that left something
 * untried with nothing to act on.
 */
class AFigureASearchForARewriteMetIsWhatItsAnswerMetTest {

    @Test
    void theFigureAWayEndedAtIsWhatItMet() {
        CompositionBudget figure = CompositionBudget.SEARCHES_A_ROW_IS_COMPOSED_THROUGH;
        CameToNothing came = Adequacy.Generated.cameToNothing(
                ReplacementDisposition.Ended.A_FIGURE_OF_THE_COMPOSING,
                ReplacementDisposition.Met.at(List.of(figure.figure())));

        assertEquals(Set.of(figure), came.met().figures());
        assertEquals(Generator.UnresolvedCombination.Reason.wordFor(Set.of(figure)),
                came.why().reason());
    }

    @Test
    void aWayThatMetNoFigureMetNothing() {
        CameToNothing came = Adequacy.Generated.cameToNothing(
                ReplacementDisposition.Ended.EVERY_ROW_ANSWERED_ALIKE,
                ReplacementDisposition.Met.AT_NO_FIGURE);

        assertTrue(came.met().nothing());
        assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                came.why().reason());
    }
}
