package souther.compiler.query;

import souther.compiler.partition.ConditionGap;
import souther.compiler.partition.DecisionReading;

import java.util.List;
import java.util.Objects;

/**
 * What the search of a rule of a decision at one place came to, and the place.
 *
 * <p>One answer of one search, and not a proof about the rule. A rule stated at several places is
 * searched at each of them, and what the rule came to is the places that answer it
 * ({@link SettledAcross}); what the composing at one was arrived at without is a list of that
 * place's conditions, and only of that place's. Held apart, the answer of one place would be
 * explained by the conditions of another — and a condition the search never met would be named as
 * one it went without.
 *
 * @param at         the place the answer came from
 * @param settlement what the search there came to
 */
public record SettledAt(DecisionReading.Ruled at, RuleSettlement settlement) {

    public SettledAt {
        Objects.requireNonNull(at, "an answer was arrived at some place of the rule");
        Objects.requireNonNull(settlement, "a place searched came to some answer");
    }

    /** The conditions of the place searched that the composing there was arrived at without. */
    public List<ConditionGap> leftOut() {
        return settlement.account().reconciledWith(at.states());
    }
}
