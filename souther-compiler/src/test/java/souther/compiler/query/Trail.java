package souther.compiler.query;

/**
 * A way down from an answer to something under it, whatever the steps are made of.
 *
 * <p>What a walk of a store steps through and what a walk of the declarations steps through are two
 * alphabets — one has no word for an arm of a sum and the other has to have one. What they share is
 * arithmetic: a way down followed by another way down, and the part of a longer way that a shorter
 * one does not cover. That is all a traversal needs to write down what it found under a thing at
 * every path that reaches the thing.
 *
 * @param <P> the kind of path this is, so the two never mix
 */
interface Trail<P extends Trail<P>> {

    /** This way down, and then {@code rest} from where it gets to. */
    P followedBy(P rest);

    /** What {@code longer} adds to this, which is the way down from where this stops. */
    P from(P longer);
}
