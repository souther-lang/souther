package souther.compiler.partition;

import souther.compiler.coverage.AlignedObservation;
import souther.compiler.observe.ObservedValue;

import java.util.List;

/**
 * The rules of a body and what the behavior takes, held together for placing runs.
 *
 * <p>Two things a caller has to hand over for every run it places, so they are one value: a rule
 * through a truth the body was handed is placed by what the row wrote, and where that is written is
 * the inputs'. Never kept in an answer of the query graph. What the inputs are made of compares by
 * identity, which {@link RulesTaken} is written not to depend on.
 *
 * @param rules  the rules of the body and where a run through each condition is recorded
 * @param inputs what the behavior takes
 */
public record RunPlacement(RulesTaken rules, BehaviorInputs inputs) {

    public RunPlacement {
        if (rules == null || inputs == null) {
            throw new IllegalArgumentException("a run is placed among some rules, over some inputs");
        }
    }

    /** Which rule a run took, given where it went and the values it was given. */
    public RulesTaken.WhichRule takenBy(AlignedObservation seen, List<ObservedValue> values) {
        return rules.takenBy(seen, values, inputs);
    }
}
