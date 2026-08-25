package souther.compiler.partition;

/**
 * How a walk over work ended.
 *
 * <p>Two ends and the difference between them is what a caller may afterwards say. A walk that ran
 * out handed over everything there was; a walk that was stopped left a piece of work in front of it
 * that nobody did. Read off a counter reaching a number instead, the two came out the same — a
 * consumer that did exactly as many pieces as it was allowed reported having stopped, over a walk
 * that had nothing more to give it.
 *
 * <p><b>Which is why the walk answers this and not the bound.</b> A bound is a fact about the
 * consumer: how many builds a class may spend, how many runs a reading may cost. Whether anything
 * was left is a fact about the walk, and only the walk was holding the piece the consumer would not
 * take.
 */
public enum Traversal {

    /** Every piece was handed over and there was no more. */
    EXHAUSTED,

    /** A piece was in front of the walk and the consumer would not do it. */
    STOPPED
}
