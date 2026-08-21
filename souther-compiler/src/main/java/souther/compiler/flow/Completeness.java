package souther.compiler.flow;

/**
 * Whether a path is one the naming could write down whole.
 *
 * <p>Not a fact about the body and not a fact about the value. A path is there and arrives whichever
 * of these it is; what differs is whether what got a run down it can be said in the naming's own
 * words, which is what a reader steering a run needs and what a reader asking what a value comes to
 * does not.
 *
 * <p>Held apart from {@link Truth} because running them together is what made a reading of the
 * numbering into a reading of the body: a comparison the numbering could not place was answered as a
 * comparison whose value was unknown, and everything downstream of it was then read as having no
 * value rather than as having one nothing could name.
 */
public enum Completeness {

    /** Every condition on the way here was named. */
    COMPLETE,

    /** Something on the way here was not, so the conditions held do not say what got a run down it. */
    PARTIAL;

    /** Complete only where both are. */
    public Completeness and(Completeness other) {
        return this == COMPLETE && other == COMPLETE ? COMPLETE : PARTIAL;
    }
}
