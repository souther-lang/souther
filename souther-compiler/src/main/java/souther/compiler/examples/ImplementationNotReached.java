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
public final class ImplementationNotReached extends RuntimeException
        implements GeneratedLinkage.Attributed {

    private static final long serialVersionUID = 1L;

    /**
     * A class missing or a method not there is what this says. What {@code cause} is the failure of,
     * this compile's classes or the other build's, is decided by whoever tried to reach the
     * implementation and is not decided here.
     */
    public ImplementationNotReached(String why, Throwable cause) {
        super(why, cause);
    }
}
