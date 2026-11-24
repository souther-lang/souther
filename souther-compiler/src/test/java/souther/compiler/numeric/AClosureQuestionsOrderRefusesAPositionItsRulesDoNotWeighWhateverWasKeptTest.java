package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static souther.compiler.numeric.RulesAsWritten.rule;
import static souther.compiler.numeric.RulesAsWritten.statedOnly;

/**
 * The order a closure question hands out refuses a position none of its rules weighs, and a walk
 * another question had kept does not change that.
 *
 * <p>The walk of a form is kept for the order the question was read off, so a form walked for one
 * question is lent to every other whose rules weigh its positions. A question whose rules do not is
 * not lent it: a form naming such a position is a reading that has gone outside the rules being
 * closed, and is told so rather than answered from what another question kept.
 */
class AClosureQuestionsOrderRefusesAPositionItsRulesDoNotWeighWhateverWasKeptTest {

    private static Granularity whole(String ignored) {
        return Granularity.DISCRETE;
    }

    private static ClosureQuestion<String> over(String text, CanonicalOrder<String> order) {
        return ClosureQuestion.of(statedOnly(List.of(rule(text)),
                AClosureQuestionsOrderRefusesAPositionItsRulesDoNotWeighWhateverWasKeptTest::whole),
                AClosureQuestionsOrderRefusesAPositionItsRulesDoNotWeighWhateverWasKeptTest::whole,
                order);
    }

    @Test
    void aFormNamingAPositionTheRulesDoNotWeighIsRefusedAlthoughItsWalkWasKept() {
        CanonicalOrder<String> kept = ClosedStates.kept().kept(CanonicalOrder.asTheyAreSpelled());
        CanonicalForm<String> form =
                new CanonicalForm<>(Map.of("a", ExactRatio.ONE, "c", ExactRatio.ONE));

        // Walked for a question that weighs both, and kept.
        assertEquals(List.of("a", "c"), form.entriesIn(over("a + b + c <= 3", kept).order())
                .stream().map(Map.Entry::getKey).toList());
        // Lent to another that weighs both.
        assertEquals(List.of("a", "c"), form.entriesIn(over("a + c <= 3", kept).order())
                .stream().map(Map.Entry::getKey).toList());
        // Not to one that does not weigh c.
        assertThrows(IllegalStateException.class,
                () -> form.entriesIn(over("a + b <= 3", kept).order()));
    }
}
