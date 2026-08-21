package souther.compiler.interaction;

import souther.compiler.coverage.ControlClaim;

/**
 * One decision of a body coming out one way, said twice: as what it takes of the inputs, and as what
 * a run that did it would be seen to have done.
 *
 * <p>Two values and not one with two readings. {@link #constrains} is the reading's own — which
 * position, which classes of it — and it is what a search for a value works from. {@link #claims} is
 * a place in the tree that runs, and it is what an observation is held against. Folded together they
 * would be one vocabulary doing both jobs, which is how a number that says where a run is recorded
 * came to be what two readings of a rule matched on.
 *
 * <p>Made together, here and nowhere else. What keeps them about the same decision is that neither
 * is looked up from the other afterwards: the walk that reads the body has the node in front of it
 * and takes both off it at once. A later pass given only the constraint would have to find the place
 * again by what it is spelled like, which is the reading being done twice and disagreeing once.
 *
 * <p>Both halves are required. A decision whose place carries no probe is one no run could ever be
 * shown to have made, so it is not one of these at all — the walk answers that it cannot name this
 * way in, and whatever was being built on it goes. Offering it instead would put a combination in
 * front of an author that every row misses however it is written.
 */
public record Decision(Condition constrains, ControlClaim claims) {

    public Decision {
        if (constrains == null || claims == null) {
            throw new IllegalArgumentException(
                    "a decision is what it takes of the inputs and what a run that made it did");
        }
    }

    @Override
    public String toString() {
        return constrains.toString();
    }
}
