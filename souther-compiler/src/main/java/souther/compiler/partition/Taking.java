package souther.compiler.partition;

/**
 * What a walk over work hands each piece to.
 *
 * <p>The consumer's answer is about the piece in front of it: it did that piece or it did not, and
 * if it did, whether that was the last one it needs. Which makes the walk's own answer exact — a
 * piece refused is a piece nobody did, and a walk that ends because a consumer is finished is not a
 * walk that left anything ({@link Traversal}).
 *
 * <p><b>What a piece costs is the consumer's to say.</b> A class counts what it built and an arm
 * counts what it ran, and a candidate the model refuses cost neither of them anything. Counted by
 * the walk instead, one bound would be spent by work the other never did.
 */
@FunctionalInterface
public interface Taking<T> {

    /** What this did with {@code each}. */
    Taken take(T each);

    /** What a consumer did with the piece in front of it. */
    enum Taken {

        /** Did it, and will take another. */
        AND_MORE,

        /** Did it, and has what it came for. */
        AND_DONE,

        /** Did not do it, which leaves it as work nobody did. */
        NOT_TAKEN
    }
}
