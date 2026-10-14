package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Figures that come back with different words, met by the walks of one search, come back with
 * what those walks came to together: that the search left something untried where any walk was
 * cut short, and otherwise what every one of them says.
 *
 * <p>Over every pair of figures that have a word, with what the pair is to say worked out from
 * the words the two say alone — so a figure given a word later is held to this without a line
 * added here.
 */
class FiguresOfTwoWalksComeBackWithWhatTheWalksCameToTogetherTest {

    private static final Generator.UnresolvedCombination.Reason CUT_SHORT =
            Generator.UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED;

    @Test
    void everyPairOfFiguresComesBackWithWhatTheirWalksCameToTogether() {
        List<CompositionBudget> worded = new ArrayList<>();
        for (CompositionBudget each : CompositionBudget.values()) {
            if (wordOf(each) != null) {
                worded.add(each);
            }
        }
        int apart = 0;
        for (CompositionBudget one : worded) {
            for (CompositionBudget other : worded) {
                if (one == other) {
                    continue;
                }
                Generator.UnresolvedCombination.Reason alone = wordOf(one);
                Generator.UnresolvedCombination.Reason besideIt = wordOf(other);
                if (alone != besideIt) {
                    apart++;
                }
                Generator.UnresolvedCombination.Reason expected =
                        alone == CUT_SHORT || besideIt == CUT_SHORT ? CUT_SHORT : alone;
                assertEquals(expected,
                        Generator.UnresolvedCombination.Reason.wordFor(Set.of(one, other)),
                        one + " (" + alone + ") met beside " + other + " (" + besideIt + ")");
            }
        }
        assertTrue(apart > 0, "every figure says one word, so no pair here was two walks apart");
    }

    /** What a walk stopped by {@code budget} alone comes back with, or null where it has none. */
    private static Generator.UnresolvedCombination.Reason wordOf(CompositionBudget budget) {
        try {
            return Generator.UnresolvedCombination.Reason.wordFor(Set.of(budget));
        } catch (IllegalArgumentException noWord) {
            return null;
        }
    }
}
