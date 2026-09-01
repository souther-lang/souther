package souther.compiler.examples;

/**
 * Where a supplied implementation is applied.
 *
 * <p>An implementation a binding supplied is the one part of a row that is not this compile's
 * computation. What it answers out of is the world the caller called from — a transaction, a
 * security or request context, an MDC, a scoped value — so it is applied there and not wherever the
 * row happens to be running. That is what this is: the application goes in, what the implementation
 * answered comes out.
 *
 * <p>The world is said and the way back to it is not. Which thread that world is on, and how a row
 * running elsewhere reaches it, are one machine's answer and are said in
 * {@code souther.compiler.execute.jvm}. A reader here asking for them would be holding one
 * arrangement's vocabulary to apply an implementation under any of them.
 *
 * <p>Every application goes through one of these. A run that applied where it stood wherever it was
 * given none would be deciding where the caller's code runs by what it was passed, which is the one
 * thing this exists to settle.
 */
public interface CallerApplication {

    /**
     * {@code application}, applied in the caller's world, and what it answered.
     *
     * <p>What it threw comes back as it was thrown. Whose failure it is and what it means for the
     * row are read where the row is, and something that wrapped it here would be a second thing to
     * unwrap — and would have the same throw read as one failure on one side of this and another on
     * the other.
     */
    Object call(Application application) throws ReflectiveOperationException;

    /**
     * One application of a supplied implementation.
     *
     * <p>Its own type rather than a {@link java.util.concurrent.Callable}, so that what it may end
     * with is what applying an implementation may end with. A callback declaring the whole of
     * {@code Exception} would leave nothing able to say that a failure arrives as it was thrown.
     */
    @FunctionalInterface
    interface Application {

        Object call() throws ReflectiveOperationException;
    }
}
