package souther.compiler.partition;

import java.util.List;
import java.util.Objects;

/**
 * One condition a rule's way consulted, with what it states about the input and asks of the
 * answers.
 *
 * <p>Kept together because they were made together. A way's account of what a row has to satisfy
 * is every step's statements one after another, and that account is what a search is composed
 * against; what the search then went without is some of those statements. Which step said one is
 * what a reader needs to find it — a helper called three times states the same comparison three
 * times at one place in the source, and only the step says which call it was — and it is known
 * only here, before the statements are run together ({@link DecisionReading.Ruled#saidOnTheWay}).
 *
 * @param shown   where a run through the condition is seen, which names the copy of the model's
 *                construct the step is
 * @param states  what the condition states about the input, in the words a composer works from
 * @param demands what it asks of the answers a row stands the dependencies in with
 */
public record RuleStep(ShownBy shown, List<OnTheWay> states, AnswersDemanded demands) {

    public RuleStep {
        Objects.requireNonNull(shown,
                "a step of a way is seen somewhere, or said to be seen nowhere");
        Objects.requireNonNull(demands, "a step asks something of the answers, or nothing");
        states = List.copyOf(states);
    }
}
