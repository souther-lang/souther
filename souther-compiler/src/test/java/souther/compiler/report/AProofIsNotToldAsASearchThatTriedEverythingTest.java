package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Generator;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reader is told about rules that leave nothing says the rules and not a search.
 *
 * <p><b>The word is a theorem and two routes reach it.</b> A walk of the whole of what the rules
 * leave that reached nothing is one; rules shown to leave nothing before anything was walked is the
 * other, and ADR-0091 admits both. What an author does about the word is the same either way, so a
 * sentence that also said how this compiler came by it is false on one of the routes — and it was,
 * from the moment the second was added.
 *
 * <p>Worth holding rather than leaving to whoever edits the sentence: a reader told that everything
 * was tried has been told the search is finished, and the one thing they might have done about it —
 * raise what the search may spend — is a thing they would then not do.
 */
class AProofIsNotToldAsASearchThatTriedEverythingTest {

    /** The words a sentence about a search uses, none of which is about what the rules leave. */
    private static final List<String> OF_A_SEARCH =
            List.of("tried", "try", "walk", "search", "stopped", "looked", "untried");

    /** The model's word says what the model leaves and nothing about how this came to know it. */
    @Test
    void theRulesLeavingNothingIsSaidWithoutASearch() {
        String said = GeneratedRows.why(
                Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE);

        assertTrue(said.contains("the rules leave no value"),
                () -> "what the model settles is what is said: " + said);
        for (String word : OF_A_SEARCH) {
            assertFalse(said.contains(word),
                    () -> "and nothing about a search, which is not what the word is about: "
                            + said + " holds " + word);
        }
    }

    /**
     * And a word about a search still says one.
     *
     * <p>The control. A check that only read the sentence above would pass a surface that had
     * stopped saying anything at all, and the difference between the two words is the whole of what
     * a reader acts on.
     */
    @Test
    void aSearchThatLeftSomethingUntriedStillSaysSo() {
        String said = GeneratedRows.why(
                Generator.UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED);

        assertTrue(OF_A_SEARCH.stream().anyMatch(said::contains),
                () -> "what this compiler did not manage is said as a search: " + said);
    }
}
