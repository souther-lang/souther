package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What came to nothing proves the rules leave nothing only over everything there was: a word that
 * proves, nothing of this compiler's met, and the plan not cut. Asked of it, whoever made it, and
 * never of the word alone.
 */
class AWordThatProvesIsTheWordOfASearchThatMetNothingTest {

    private static final Set<CompositionBudget> SEARCHES =
            Set.of(CompositionBudget.SEARCHES_A_ROW_IS_COMPOSED_THROUGH);

    private static final Generator.UnresolvedCombination PROVED =
            new Generator.UnresolvedCombination(List.of("days=low"),
                    Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE);

    @Test
    void aProofOverEverythingThereWasProves() {
        assertTrue(CameToNothing.metNothing(PROVED).proves());
    }

    @Test
    void aProofBesideAFigureMetOrAPlanCutProvesNothing() {
        assertFalse(new CameToNothing(PROVED, CompositionShortfall.of(SEARCHES), Set.of())
                .proves(), "met on the way");
        assertFalse(new CameToNothing(PROVED, CompositionShortfall.NONE, SEARCHES).proves(),
                "over a plan cut short");
    }

    @Test
    void aProofThatAlsoMetAFigureIsSaidInTheFiguresWord() {
        CameToNothing cut = CameToNothing.metNothing(PROVED)
                .alsoMet(CompositionShortfall.of(SEARCHES));

        assertFalse(cut.proves());
        assertEquals(Generator.UnresolvedCombination.Reason.wordFor(SEARCHES), cut.why().reason());
        assertEquals(CompositionShortfall.of(SEARCHES), cut.met());
        assertEquals(PROVED.classes(), cut.why().classes());
    }

    @Test
    void nothingMoreMetIsThisOne() {
        CameToNothing proved = CameToNothing.metNothing(PROVED);
        assertSame(proved, proved.alsoMet(CompositionShortfall.NONE));
    }
}
