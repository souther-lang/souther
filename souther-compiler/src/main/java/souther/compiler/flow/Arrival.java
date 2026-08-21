package souther.compiler.flow;

/**
 * One way an expression arrives at a value: what it comes to, and what got a run there.
 *
 * <p>A value, and compared as one. Two arrivals that say the same thing are one way and not two, so
 * a reading that produced the same way twice offers nothing twice — which is what keeps a count of
 * these a count of what the body does rather than a count of how the reading got there.
 *
 * @param value      what the path comes to, where this reading can say
 * @param provenance what got a run down it, in the naming's words
 */
public record Arrival<P>(Truth value, Provenance<P> provenance) {

    public Arrival {
        if (value == null || provenance == null) {
            throw new IllegalArgumentException("an arrival is a value reached by a path");
        }
    }

    public P path() {
        return provenance.path();
    }

    public boolean isComplete() {
        return provenance.isComplete();
    }
}
