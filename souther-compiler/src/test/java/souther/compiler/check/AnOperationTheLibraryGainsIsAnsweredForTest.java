package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.stdlib.Stdlib;
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
 * in range of a question by what it is declared to be, and one in range has exactly one answer — a
 * rule, or its name among the ones there is nothing to say of, and never both. Adding an operation
 * to the library therefore fails this until someone decides which, and the decision is written where
 * the next reader will find it.
 *
 * <p>What is <em>not</em> asked here is whether the number an operation answers is read by more than
 * one representation. That is a property of the declarations and holds of every operation, in range
 * of a question or not, so it is held over the declarations themselves
 * ({@link ANumberIsReadByAtMostOneRepresentationTest}). Asked here, how far the exclusivity
 * reached would be whatever a range happened to cover that week.
 *
 * <p>A question whose answer is read off the declaration ({@link Question#COMBINATOR}) is held the
 * same way and for the same reason: the derivation answering for most of its range does not make a
 * signature it gets nothing out of a gap rather than a decision.
 */
class AnOperationTheLibraryGainsIsAnsweredForTest {

    /**
     * One of the two, and not one or the other.
     *
     * <p>A rule and a silence are not two ways of covering a range. A silence says that nothing is
     * true of the operation under the subject, so beside a rule saying what is, it is the denial of
     * what the rule says and one of the two is wrong. Asked as "a rule <em>or</em> a silence", a
     * silence that has become false stays where it is: {@code Int.add} declared to say nothing of
     * what it answers in what it was given, beside the arithmetic the language reads it as, covers
     * the range as well as anything, and covering the range is all that such a question asks.
     *
     * <p>A rule may be one another proposition already gives. What answers a question is what
     * {@link Question#answeredFor} says, which for some of them is derived from a fact declared
     * under a different subject; what is written down <em>for</em> a question is
     * {@link Question#answeredOperations}, and the two are kept apart on purpose. So the
     * contradiction between a rule and a silence is read here, over the range, rather than off the
     * rows — read off the rows, an operation answered by another proposition and silenced here would
     * be in neither list and would go unseen.
     */
    @Test
    void everyOperationInAQuestionsRangeAnswersItOneWayAndNotBoth() {
        List<String> unsettled = new ArrayList<>();
        for (Map.Entry<ValueName.Stdlib.Operation, Stdlib.Entry> e
                : DefaultStdlib.get().entries().entrySet()) {
            ValueName operation = e.getKey();
            for (Question question : Question.askedOf(DefaultStdlib.get(), e.getValue().signature())) {
                boolean answered = question.answeredFor(DefaultStdlib.get(), operation);
                boolean silent = question.nothingSaidOf().contains(operation);
                if (answered != silent) {
                    continue;
                }
                unsettled.add(e.getKey() + " — " + question
                        + (answered ? " (a rule and a silence beside it)" : " (neither)"));
            }
        }
        assertEquals(List.of(), unsettled,
                "these operations are in range of a question and do not answer it exactly once —"
                        + " with neither a rule nor a name among the ones there is nothing to say"
                        + " of, or with both, where the silence denies the rule");
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
                if (!question.asksOfOperation(DefaultStdlib.get(), operation)) {
                    unasked.add(operation + " — " + question + " (a rule)");
                }
            }
            for (ValueName operation : question.nothingSaidOf()) {
                if (!question.asksOfOperation(DefaultStdlib.get(), operation)) {
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
        Stdlib.Signature leavesItsResultToItsBody = new Stdlib.Signature(
                List.of(new Type.FnOf(List.of(Type.Prim.INT), Type.Prim.INT), Type.Prim.INT), null);
        assertEquals(List.of(Question.COMBINATOR), Question.askedOf(DefaultStdlib.get(), leavesItsResultToItsBody),
                "an operation that takes a function is asked what it hands it, whatever it leaves"
                        + " unsaid about what it answers");
    }
}
