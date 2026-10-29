package souther.compiler.examples;

import souther.compiler.generated.GeneratedLinkage;

/**
 * The answerer could not reach the implementation it applies.
 *
 * <p>Not the applied code failing, which is {@link InvocationFailure}. The class is not in the loader,
 * the constructor does not take what it was expected to take, the {@code apply} of that arity is not
 * there — for the compile's own answerer every one of those is this compiler failing to reach what it
 * emitted, and for one supplied from outside it is that implementation not being what it was said to
 * be.
 *
 * <p>Separate from {@link InvocationFailure} so that a reader deciding whose failure a row met is not
 * left to tell them apart by what the throwable happens to be. What the row makes of one is the row's,
 * and today it makes the same thing of this as it made when the two arrived as one.
 */
public final class ImplementationNotReached extends RuntimeException {

    private static final long serialVersionUID = 1L;

    /**
     * A class missing or a method not there is what this says. A generated class that will not
     * link, held in {@code cause} or under it, is not a way of not being reached: it is this
     * compiler's output failing, and is raised as such.
     */
    public ImplementationNotReached(String why, Throwable cause) {
        GeneratedLinkage.rejectDefect(cause);
        super(why, cause);
    }
}
