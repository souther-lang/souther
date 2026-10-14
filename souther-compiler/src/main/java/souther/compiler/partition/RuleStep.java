package souther.compiler.partition;

import java.util.List;
import java.util.Objects;

/**
 * One condition a rule's way consulted, with what it states about the input and asks of the
 * answers.
 *
 * <p>Kept together because they were made together. A way's account of what a row has to satisfy
 * is every step's statements one after another, and that account is what a search is composed
 * against; what the search then went without is some of those statements. Which calls a statement
 * was read off is what a reader needs to find it — a helper called three times states the same
 * comparison three times at one place in the source — and it is carried here, with the statements,
 * from where they were read ({@link DecisionReading.Ruled#saidOnTheWay}).
 *
 * @param shown   where a run through the condition is seen, which names the copy of the model's
 *                construct the step is
 * @param states  what the condition states about the input, in the words a composer works from
 * @param demands what it asks of the answers a row stands the dependencies in with
 * @param said    which copies of the model's code each thing it states and asks was read off,
 *                told where the condition was read. Not where the step is seen: a comparison over
 *                a value another call worked out states what that call's fork decided, and the
 *                halves of a joined condition may stand in two calls
 */
public record RuleStep(ShownBy shown, List<OnTheWay> states, AnswersDemanded demands,
                       SaidOnTheWay said) {

    public RuleStep {
        Objects.requireNonNull(shown,
                "a step of a way is seen somewhere, or said to be seen nowhere");
        Objects.requireNonNull(demands, "a step asks something of the answers, or nothing");
        Objects.requireNonNull(said, "what a step's statements were read off, or nothing");
        states = List.copyOf(states);
    }
}
