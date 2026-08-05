package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the checks know of the library's operations is written in the checks, away from the
 * declarations it is about. So an operation the library gains changes nothing in them, and the
 * change that should have been made is missing rather than wrong: the totality check quietly stops
 * crediting an element, or a guard quietly stops discharging a clause. That is how
 * {@code List.distinctBy} came to be in neither of the two combinator tables it belonged in.
 *
 * <p>Here each question a rule answers is held to its range. An operation the library declares is in
 * range of a question by what it is declared to be, and one in range has an answer — a rule, or its
 * name among the ones there is nothing to say of. Adding an operation to the library therefore fails
 * this until someone decides which, and the decision is written where the next reader will find it.
 *
 * <p>What a combinator hands its closure is not among these questions: it is read off the signature
 * ({@link Combinators}), so an operation the library gains answers it by being declared.
 */
class AnOperationTheLibraryGainsIsAnsweredForTest {

    @Test
    void everyOperationInAQuestionsRangeAnswersIt() {
        List<String> unanswered = new ArrayList<>();
        for (Map.Entry<String, Prelude.PreludeEntry> e : Prelude.entries().entrySet()) {
            ValueName operation = new ValueName.Stdlib(e.getKey());
            for (DischargeRules.Question question : DischargeRules.asked(e.getValue().signature())) {
                if (DischargeRules.answers(operation, question)
                        || DischargeRules.nothingToSay(operation, question)) {
                    continue;
                }
                unanswered.add(e.getKey() + " — " + question);
            }
        }
        assertTrue(unanswered.isEmpty(),
                "these operations are in range of a question and answer it neither with a rule nor by"
                        + " being named as one there is nothing to say of:\n  "
                        + String.join("\n  ", unanswered));
    }

    /**
     * The other way round: a name said to have nothing to say must be in range of the question it is
     * said that of, or it is a name nobody will ever look up — a library operation that was renamed
     * or removed, or a question whose range moved out from under it.
     */
    @Test
    void nothingIsSaidOfAnOperationNoQuestionIsAskedOf() {
        for (DischargeRules.Question question : DischargeRules.Question.values()) {
            for (ValueName operation : DischargeRules.nothingSaidOf(question)) {
                Prelude.PreludeEntry entry = Prelude.entry(operation.name());
                assertTrue(entry != null && DischargeRules.asked(entry.signature()).contains(question),
                        operation.name() + " is said to have nothing to say about " + question
                                + ", and is not an operation that question is asked of");
            }
        }
    }
}
