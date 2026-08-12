package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the checks know of the library's operations is written in the checks, away from the
 * declarations it is about. So an operation the library gains changes nothing in them, and the
 * change that should have been made is missing rather than wrong: the totality check quietly stops
 * crediting an element, or a guard quietly stops discharging a clause. That is how
 * {@code List.distinctBy} came to be in neither of the two combinator tables it belonged in.
 *
 * <p>Here every question is held to its range, both ways round. An operation the library declares is
 * in range of a question by what it is declared to be, and one in range has an answer — a rule, or
 * its name among the ones there is nothing to say of. Adding an operation to the library therefore
 * fails this until someone decides which, and the decision is written where the next reader will
 * find it.
 *
 * <p>A question whose answer is read off the declaration ({@link Question#COMBINATOR}) is held the
 * same way and for the same reason: the derivation answering for most of its range does not make a
 * signature it gets nothing out of a gap rather than a decision.
 */
class AnOperationTheLibraryGainsIsAnsweredForTest {

    @Test
    void everyOperationInAQuestionsRangeAnswersIt() {
        List<String> unanswered = new ArrayList<>();
        for (Map.Entry<String, Prelude.PreludeEntry> e : Prelude.entries().entrySet()) {
            ValueName operation = Prelude.operation(e.getKey());
            for (Question question : Question.askedOf(e.getValue().signature())) {
                if (question.answeredFor(operation)
                        || question.nothingSaidOf().contains(operation)) {
                    continue;
                }
                unanswered.add(e.getKey() + " — " + question);
            }
        }
        assertEquals(List.of(), unanswered,
                "these operations are in range of a question and answer it neither with a rule nor by"
                        + " being named as one there is nothing to say of");
    }

    /**
     * The other way round: every name written down must be one the question is asked of, whether it
     * was written as a rule or as a silence. A table keyed by a name takes any name, so a row under
     * one nothing asks is a row nothing reaches — a library operation that was renamed or removed,
     * or a question whose range moved out from under it. Both directions are the same defect seen
     * from the two ends, so both are read off the tables themselves rather than off what the library
     * happens to declare today.
     */
    @Test
    void everyOperationWrittenDownIsOneTheQuestionIsAskedOf() {
        List<String> unasked = new ArrayList<>();
        for (Question question : Question.values()) {
            for (ValueName operation : question.answeredOperations()) {
                if (!question.asksOfOperation(operation.toString())) {
                    unasked.add(operation + " — " + question + " (a rule)");
                }
            }
            for (ValueName operation : question.nothingSaidOf()) {
                if (!question.asksOfOperation(operation.toString())) {
                    unasked.add(operation + " — " + question + " (nothing to say)");
                }
            }
        }
        assertEquals(List.of(), unasked,
                "these are written down against a question they are not asked");
    }

    /**
     * A question reads the declaration for what it asks about and no more. What an operation hands
     * its closure is a question about its arguments, so a declaration that leaves its result to its
     * body — which the library allows a helper with parameters to do — is still asked it. Nothing in
     * the library takes that shape today, and a range is meant to hold an operation nobody thought
     * of, so it is held to a signature written here rather than to one the library declares.
     */
    @Test
    void aDeclarationThatWritesNoReturnTypeIsStillAskedWhatItHandsItsClosure() {
        Prelude.Signature leavesItsResultToItsBody = new Prelude.Signature(
                List.of(new Type.FnOf(List.of(Type.Prim.INT), Type.Prim.INT), Type.Prim.INT), null);
        assertEquals(List.of(Question.COMBINATOR), Question.askedOf(leavesItsResultToItsBody),
                "an operation that takes a function is asked what it hands it, whatever it leaves"
                        + " unsaid about what it answers");
    }
}
