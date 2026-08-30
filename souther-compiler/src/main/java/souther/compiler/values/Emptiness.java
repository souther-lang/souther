package souther.compiler.values;

/**
 * Whether a position admits anything, as far as that can be said without building.
 *
 * <p>Three answers and not two, because a reading that has said what a position admits has not
 * always worked out what that comes to. A plan naming two patterns admits whatever their strings
 * have in common, and which strings those are is a machine somebody has to make — so until it is
 * made, the honest answer is neither yes nor no.
 *
 * <p><b>{@link #UNDECIDED} is not "no".</b> A reader that took it for one would drop a branch
 * nothing had shown impossible, and one that took it for the other would keep a branch and call the
 * reading exact. What it means is that the decision has to wait: the whole of what the position
 * admits is not described yet, and deciding now would decide on less than the rules say.
 *
 * <p>Which is the whole reason it exists. Answered as a boolean, the only way to be honest was to
 * build the machine there and then — and what a branch costs to decide would depend on where the
 * author put the brackets, since what is in hand at that moment is what the walk happened to have
 * reached.
 */
public enum Emptiness {

    /** Nothing is admitted, and that is settled. */
    EMPTY,

    /** Something is admitted, and that is settled. */
    NONEMPTY,

    /** Neither, until what the position admits has been worked out. */
    UNDECIDED;

    /** Whether this is the settled answer that nothing is admitted. */
    public boolean isEmpty() {
        return this == EMPTY;
    }

    /**
     * What a choice between two comes to.
     *
     * <p>Something is admitted where either side admits something, and nothing where both admit
     * nothing. Where one is settled empty and the other is not known, the choice is what the other
     * one is — which is not known either.
     */
    public Emptiness joined(Emptiness other) {
        if (this == NONEMPTY || other == NONEMPTY) {
            return NONEMPTY;
        }
        return this == EMPTY && other == EMPTY ? EMPTY : UNDECIDED;
    }
}
