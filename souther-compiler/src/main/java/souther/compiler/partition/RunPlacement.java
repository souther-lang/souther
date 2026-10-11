package souther.compiler.partition;

import souther.compiler.coverage.AlignedObservation;
import souther.compiler.observe.ObservedValue;
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

    /**
     * Which rule a run took.
     *
     * <p>Of a row something watched: a caller holding one nothing watched has no run to place and
     * says so before asking. The values the row was given are evidence of a rule only where the
     * behavior answered; a row stopped before the behavior was applied has them all the same, and
     * so does one that went down part of a path and no further.
     *
     * @throws IllegalArgumentException where nothing watched the row
     */
    public RulesTaken.WhichRule takenBy(ObservedInputs row) {
        if (!(row.watched() instanceof Generator.Watched.Ran(AlignedObservation seen))) {
            throw new IllegalArgumentException("a run nothing watched is placed nowhere");
        }
        List<ObservedValue> values = row.answered() ? row.inputs() : List.of();
        return rules.takenBy(seen, values, inputs);
    }
}
