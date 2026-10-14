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
 * @param seen    every place a run through the condition is seen on the way, each naming the
 *                copy of the model's construct it is — one condition met at two calls of a helper
 *                is one step seen at both. Never empty
 * @param states  what the condition states about the input, in the words a composer works from
 * @param demands what it asks of the answers a row stands the dependencies in with
 * @param said    which copies of the model's code each thing it states and asks was read off,
 *                told where the condition was read, at every place it was. Not where the step is
 *                seen: a comparison over a value another call worked out states what that call's
 *                fork decided, and the halves of a joined condition may stand in two calls
 */
public record RuleStep(List<ShownBy> seen, List<OnTheWay> states, AnswersDemanded demands,
                       SaidOnTheWay said) {

    public RuleStep {
        if (seen == null || seen.isEmpty()) {
            throw new IllegalArgumentException(
                    "a step of a way is seen somewhere, or said to be seen nowhere");
        }
        Objects.requireNonNull(demands, "a step asks something of the answers, or nothing");
        Objects.requireNonNull(said, "what a step's statements were read off, or nothing");
        seen = List.copyOf(seen);
        states = List.copyOf(states);
    }

    /** The step consulted once, seen at {@code shown}. */
    public RuleStep(ShownBy shown, List<OnTheWay> states, AnswersDemanded demands,
                    SaidOnTheWay said) {
        this(List.of(shown), states, demands, said);
    }

    /** Where the condition is witnessed: the first place the way met it, which a run that took
     *  the way went through. */
    public ShownBy shown() {
        return seen.getFirst();
    }
}
