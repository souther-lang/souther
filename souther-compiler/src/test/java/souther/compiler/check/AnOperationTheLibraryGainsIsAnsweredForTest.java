package souther.compiler.check;

import souther.compiler.Prelude;
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
            ValueName operation = new ValueName.Stdlib(e.getKey());
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
     * The other way round: a name said to have nothing to say must be in range of the question it is
     * said that of, or it is a name nobody will ever look up — a library operation that was renamed
     * or removed, or a question whose range moved out from under it.
     */
    @Test
    void nothingIsSaidOfAnOperationNoQuestionIsAskedOf() {
        List<String> outOfRange = new ArrayList<>();
        for (Question question : Question.values()) {
            for (ValueName operation : question.nothingSaidOf()) {
                Prelude.PreludeEntry entry = Prelude.entry(operation.name());
                if (entry == null || !Question.askedOf(entry.signature()).contains(question)) {
                    outOfRange.add(operation.name() + " — " + question);
                }
            }
        }
        assertEquals(List.of(), outOfRange,
                "these are said to have nothing to say about a question they are not asked");
    }

    /**
     * And a rule answers a question it is in range of. A table keyed by name takes any name, so a
     * rule under one the question is not asked of is a rule nothing reaches — the same silence from
     * the other end.
     */
    @Test
    void everyRuleAnswersAQuestionItsOperationIsAsked() {
        List<String> unasked = new ArrayList<>();
        for (Question question : Question.values()) {
            for (Map.Entry<String, Prelude.PreludeEntry> e : Prelude.entries().entrySet()) {
                ValueName operation = new ValueName.Stdlib(e.getKey());
                if (question.answeredFor(operation)
                        && !Question.askedOf(e.getValue().signature()).contains(question)) {
                    unasked.add(e.getKey() + " — " + question);
                }
            }
        }
        assertEquals(List.of(), unasked,
                "these have a rule answering a question they are not in range of");
    }
}
