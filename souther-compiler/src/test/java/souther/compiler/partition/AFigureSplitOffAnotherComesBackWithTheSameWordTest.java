package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two figures bounding two halves of one walk come back with one word.
 *
 * <p>What a stopped walk says is the walk's own answer; the figures it met travel beside it and do
 * not choose it ({@link Realization.Unknown}). So a figure split off another inherits that answer —
 * filed under a second word, one walk says two things depending on which of its own numbers ran out
 * first, and an answer carrying the word and the budget cannot be assembled at all.
 *
 * <p><b>Over the figures themselves rather than over the two that exist today.</b> The pairing is
 * what {@link CompositionBudget#splitFrom} states, and a figure split off another later is held to
 * this without anyone adding a line here. Written as a case per pair, the check would be one more
 * place to remember at the moment a split is made, which is the moment it was already forgotten
 * once.
 */
class AFigureSplitOffAnotherComesBackWithTheSameWordTest {

    @Test
    void everyFigureSplitOffAnotherSaysWhatThatOneSays() {
        int pairs = 0;
        for (CompositionBudget each : CompositionBudget.values()) {
            CompositionBudget from = each.splitFrom();
            if (from == null) {
                continue;
            }
            pairs++;
            assertEquals(wordOf(from), wordOf(each),
                    each + " was split off " + from + " and does not come back saying what it"
                            + " says");
            // And a walk that met both is one walk, so the two together read as one word too.
            assertEquals(wordOf(from), wordOf(Set.of(each, from)),
                    "a walk that met both halves of one figure says what that walk says");
        }
        assertTrue(pairs > 0, "no figure says it was split off another, so this checked nothing");
    }

    /**
     * The figures that were not split off anything are not all one word, which is what makes the
     * check above say something.
     *
     * <p>Without it, a {@code wordFor} that answered the same for every figure would pass — and so
     * would one that threw for all of them.
     */
    @Test
    void andTheFiguresAreNotAllOneWordAnyway() {
        assertNotEquals(wordOf(CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT),
                wordOf(CompositionBudget.VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED),
                "two figures a search comes back from say different things");
        assertThrows(IllegalArgumentException.class,
                () -> Generator.UnresolvedCombination.Reason.wordFor(
                        Set.of(CompositionBudget.PATHS_OF_A_DECISION_READ)),
                "and a figure no search comes back from has no word at all");
    }

    /** What a walk stopped by these comes back with, or the refusal where they have no word. */
    private static Object wordOf(Set<CompositionBudget> budgets) {
        try {
            return Generator.UnresolvedCombination.Reason.wordFor(budgets);
        } catch (IllegalArgumentException refused) {
            return "no word";
        }
    }

    private static Object wordOf(CompositionBudget budget) {
        return wordOf(Set.of(budget));
    }
}
