package souther.compiler.inputs;

import java.util.List;
import java.util.Objects;

/**
 * What showed that a run on the way to a rule stops at a construction, as a finding carries it:
 * what the construction asks that the way to the rule does not hold, and the value of the input
 * the proof rested on — the whole number at each place of the input that value is asked to hold,
 * and anything at the rest.
 *
 * <p>The published account of a proof, and not the proof, as {@link AStopShown} is of a stop in an
 * operation. The proof is made by the stop assessment of the constructions on the way to a
 * comparison and by nothing else, once a value is shown to exist, to take the way to the rule, to
 * get to the construction with nothing before it ending the run, and not to meet what the
 * construction asks. Building one of these shows nothing.
 *
 * @param asks what the construction asks, as a finding that it is not resolved would say it
 * @param at   the number at each place the value is asked to hold, in the order the input
 *             declares its places; none where no run meets what is asked
 */
public record AConstructionStopShown(WhatAConstructionAsks asks, List<AStopShown.NumberAt> at) {

    public AConstructionStopShown {
        Objects.requireNonNull(asks, "a stop is shown at some construction");
        at = List.copyOf(at);
    }
}
