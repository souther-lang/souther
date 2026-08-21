package souther.compiler.interaction;

import java.util.List;

/**
 * One way a decision can be settled, as the conditions that hold when it is.
 *
 * <p>Several conditions and not one, because a decision reached under another decision is settled
 * by both: the comparison on the total is a decision only where the member is Standard, and an
 * outcome naming the comparison alone would name a combination the body has no path to.
 */
public record Outcome(List<Decision> holds) {

    public Outcome {
        holds = List.copyOf(holds);
    }

    /** What a run that settled the decision this way would be seen to have done. */
    public List<souther.compiler.coverage.ControlClaim> claims() {
        return holds.stream().map(Decision::claims).toList();
    }

    @Override
    public String toString() {
        return String.join(" & ", holds.stream().map(Object::toString).toList());
    }
}
