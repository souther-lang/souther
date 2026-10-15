package souther.compiler.query;

import souther.compiler.coverage.ControlPlace;
import souther.compiler.partition.ConditionGap;
import souther.compiler.partition.DecisionReading;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

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
 * @param shownWrong the places a proof that nothing arrives was about that would have left this
 *                   place no row, and that a row went through — which is why the place was asked
 *                   at all. Empty where no such proof was on its way, and always where the place
 *                   is excluded: what excludes it then is something that stands. The proofs are
 *                   the reading's ({@link Adequacy.Arrived}) and these are which of them this
 *                   place rested on
 */
public record SettledAt(DecisionReading.Ruled at, RuleSettlement settlement,
                        Set<ControlPlace> shownWrong) {

    public SettledAt {
        Objects.requireNonNull(at, "an answer was arrived at some place of the rule");
        Objects.requireNonNull(settlement, "a place searched came to some answer");
        shownWrong = Collections.unmodifiableSet(new LinkedHashSet<>(shownWrong));
        if (!shownWrong.isEmpty() && settlement.requirement() instanceof RuleRequirement.Excluded) {
            throw new IllegalArgumentException("a place excluded is excluded by a proof that"
                    + " stands, and no proof taken back is why it is owed nothing: " + shownWrong);
        }
    }

    /** The conditions of the place searched that the composing there was arrived at without. */
    public List<ConditionGap> leftOut() {
        return settlement.account().reconciledWith(at.states());
    }
}
