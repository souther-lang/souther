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
 * only here, before the statements are run together.
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

    /**
     * Whether {@code gap} is about something this step said.
     *
     * <p>Asked of the values the step made and of nothing else. A gap holds the entry or the demand
     * it is about, and that value came off one or more steps; one asked by two steps — two calls
     * asking one thing of a row — is about both. Inside an alternative as much as beside one,
     * which is where a condition whose value is one of several things puts what it asks.
     */
    public boolean said(ConditionGap gap) {
        return switch (gap) {
            case ConditionGap.OfTheInput(ReachabilityGap.Unstated(var declined)) ->
                    holds(states, declined);
            case ConditionGap.OfTheInput(ReachabilityGap.Uncomposed(var taken, var _)) ->
                    holds(states, taken);
            case ConditionGap.OfTheInput(ReachabilityGap.LookedAlongWhole(var oneOf, var _)) ->
                    holds(states, oneOf);
            case ConditionGap.OfTheInput(ReachabilityGap.ProvedImpossible(var taken)) ->
                    holds(states, taken);
            case ConditionGap.OfADemand(DemandGap.Unstated unstated) ->
                    demands.declined().contains(unstated);
            case ConditionGap.OfADemand(DemandGap.Uncomposed(var demand, var _)) ->
                    demands.stated().contains(demand);
        };
    }

    private static boolean holds(List<OnTheWay> entries, OnTheWay wanted) {
        for (OnTheWay each : entries) {
            if (each.equals(wanted)) {
                return true;
            }
            if (each instanceof OnTheWay.OneOf several
                    && several.alternatives().stream().anyMatch(one -> holds(one, wanted))) {
                return true;
            }
        }
        return false;
    }
}
