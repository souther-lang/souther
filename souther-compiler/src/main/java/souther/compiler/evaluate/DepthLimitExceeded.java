package souther.compiler.evaluate;

/**
 * A recursive helper the evaluation reaches went deeper than the policy allows.
 *
 * <p>Reached before the stack runs out, which is why it exists: how deep a stack goes before it is
 * gone depends on the size of the frames on it, and that depends on the helper and on whether the JVM
 * has compiled it yet. A model whose depth is decided that way compiles on one machine and not on
 * another.
 *
 * <p>Carries no stack trace and is a single instance, for {@link StepLimitExceeded}'s reason and one
 * more: it is thrown at a depth of thousands of frames, and filling in a trace there is the one thing
 * a stack this deep is worst at.
 */
public final class DepthLimitExceeded extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /**
     * The one of these there is.
     *
     * <p>Shared safely because it holds nothing about the throw that reached it: the constructor
     * asks for no trace and no suppression, so what a second instance would carry beyond this one
     * is nothing.
     */
    @SuppressWarnings("StaticAssignmentOfThrowable")
    public static final DepthLimitExceeded INSTANCE = new DepthLimitExceeded();

    private DepthLimitExceeded() {
        super("the evaluation reached its recursion depth limit", null, false, false);
    }
}
