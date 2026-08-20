package souther.compiler.interaction;

import java.util.List;

/**
 * One of the values an interaction is made of, and the ways it can be settled.
 *
 * <p>What varies together, not what forks. Nested decisions inside one operand are one factor of as
 * many outcomes as the operand has paths to a value, rather than one factor each: the refinement
 * they stand in is what says which of their combinations the body has, and enumerating them apart
 * would offer rows for combinations no path reaches.
 */
public record Factor(List<Outcome> outcomes) {

    public Factor {
        outcomes = List.copyOf(outcomes);
    }

    @Override
    public String toString() {
        return outcomes.toString();
    }
}
