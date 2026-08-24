package souther.compiler.reading;

import souther.compiler.coverage.ControlClaim;

import java.util.List;

/**
 * One way to a place in the body: the decisions that hold on the way there, all of them at once.
 *
 * <p>A conjunction, and the type is where that is said. Which decisions hold together on one way
 * and which ways there are of getting somewhere are two different things, and written as a list of
 * lists they are told apart by which bracket a reader is looking at — so a caller that flattened one
 * level had a disjunction where it thought it had a conjunction, and nothing said otherwise.
 *
 * <p>Empty is a way and not the absence of one. The body itself is reached with nothing having to
 * hold, which is this with no decisions in it; a place nothing reaches has no {@code WayIn} at all
 * and is said in {@link PathAccess}.
 *
 * <p>Both halves of each decision travel here. {@link #conditions()} is what a search for values
 * works from and {@link #claims()} is what a run that came this way would be seen to have done —
 * the same pair {@link Decision} keeps, and neither is looked up from the other afterwards.
 */
public record WayIn(List<Decision> decisions) {

    public WayIn {
        decisions = List.copyOf(decisions);
    }

    /** What this way takes of the inputs, which is what a row is steered by. */
    public List<Condition> conditions() {
        return decisions.stream().map(Decision::constrains).toList();
    }

    /** What a run that came this way would be seen to have done. */
    public List<ControlClaim> claims() {
        return decisions.stream().map(Decision::claims).toList();
    }

    @Override
    public String toString() {
        return decisions.toString();
    }
}
