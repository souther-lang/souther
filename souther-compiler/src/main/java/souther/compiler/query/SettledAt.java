package souther.compiler.query;

import souther.compiler.partition.ConditionGap;
import souther.compiler.partition.DecisionReading;

import java.util.List;
import java.util.Objects;

/**
 * What a rule of a decision came to, and the place it was searched at that answer came from.
 *
 * <p>One answer of one search, and not a proof about the rule. A rule stated at several places is
 * searched at each of them and settled by whichever established the most
 * ({@link Adequacy.DecisionSearch#acrossThePlaces}); what the composing there was arrived at without
 * is a list of that place's conditions, and only of that place's. Held apart, the answer of one place
 * would be explained by the conditions of another — and a condition the search never met would be
 * named as one it went without.
 *
 * <p>A rule every place of which the model leaves no row is excluded over all of them together;
 * the place held then is the one whose answer is carried, which says nothing the others did not.
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
