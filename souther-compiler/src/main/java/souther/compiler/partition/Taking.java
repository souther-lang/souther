package souther.compiler.partition;

/**
 * What a walk over work hands each piece to.
 *
 * <p>The consumer's answer is about the piece in front of it and nothing else: it did that piece, or
 * it did not. Which makes the walk's own answer exact — a piece refused is a piece nobody did, so
 * there is no guessing at whether anything was left ({@link Traversal}).
 *
 * <p><b>What a piece costs is the consumer's to say.</b> A class counts what it built and an arm
 * counts what it ran, and a candidate the model refuses cost neither of them anything. Counted by
 * the walk instead, one bound would be spent by work the other never did.
 */
@FunctionalInterface
public interface Taking<T> {

    /**
     * Whether this took {@code each}.
     *
     * <p>False leaves it undone, which is what makes the walk {@link Traversal#STOPPED}. A consumer
     * that has what it came for says so the same way: it is not taking this one either, and what it
     * found is its own to hand back.
     */
    boolean take(T each);
}
