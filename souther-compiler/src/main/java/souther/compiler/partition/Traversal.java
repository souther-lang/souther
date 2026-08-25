package souther.compiler.partition;

/**
 * How a walk over work ended.
 *
 * <p>Three ends, because two of them are a walk that stopped and only one of them is a walk that
 * left something undone. A walk that ran out handed over everything there was; a walk a consumer
 * ended because it had what it came for handed over everything it needed; a walk a consumer refused
 * left a piece in front of it that nobody did. Only the third says the search was incomplete.
 *
 * <p>Held as two, the third had to be told from the second by looking at whether the consumer was
 * holding an answer — which is a value whose meaning is somewhere else, and the next caller to read
 * {@code STOPPED} as "something was left" would be right about the name and wrong about the run.
 *
 * <p><b>Which is why the walk answers this and not the bound.</b> A bound is a fact about the
 * consumer: how many builds a class may spend, how many runs a reading may cost. Whether anything
 * was left is a fact about the walk, and only the walk was holding the piece the consumer refused.
 */
public enum Traversal {

    /** Every piece was handed over and there was no more. */
    EXHAUSTED,

    /** A consumer took a piece and had what it came for. Nothing was left undone; there was simply
     *  no reason to go on. */
    SATISFIED,

    /** A piece was in front of the walk and the consumer would not do it. The one end that makes a
     *  search incomplete. */
    STOPPED
}
