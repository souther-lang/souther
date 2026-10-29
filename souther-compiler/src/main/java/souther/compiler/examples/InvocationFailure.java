package souther.compiler.examples;

import souther.compiler.generated.GeneratedLinkage;

/**
 * What a generated method ended with, carried out of the invocation that made it.
 *
 * <p>Transport and nothing else. It says that code this compile generated was applied and came back
 * with a {@code cause}, and it says nothing about what that means — not whose failure it is, not
 * whether the row can go on, not which of the things a row does was being done. Those are answered
 * where the row is evaluated, which is what holds the phase it was in and the position it was at.
 *
 * <p>Named for the transport rather than for any of its readings on purpose. A wrapper called a
 * fixture failure or a helper failure would be the reflection that made it deciding what the row is
 * told, which is the shape this exists to remove: the same failure raised through the method a row
 * operand is emitted as and through the method a helper is emitted as arrives here the one way, and
 * the caller assigns the meaning.
 *
 * <p>Not everything a reflective call can end with is one of these. A class that will not load, a
 * method that is not there and an access that is refused are this compiler failing to reach its own
 * output rather than the output failing; where a behavior is applied that is
 * {@link ImplementationNotReached}, and where a fixture's helper is run it keeps the reading it had.
 *
 * <p>Public because what applies a behavior is given to a run ({@link Answerer}), and an answerer
 * outside this package carries what it applied out the same way.
 */
public final class InvocationFailure extends RuntimeException implements GeneratedLinkage.Attributed {

    private static final long serialVersionUID = 1L;

    /**
     * Carries {@code cause} out as it stands. Whose code ended with it is not decided here, because
     * what is applied may be supplied from outside, and a link failure of a supplied implementation
     * is that implementation failing. Code of this compile is carried by {@link #ofGeneratedCode}.
     */
    public InvocationFailure(Throwable cause) {
        super(cause == null ? "the invocation ended with no cause" : cause.toString(), cause);
    }

    /**
     * What a generated class of this compile ended with, carried out.
     *
     * <p>The one place that says the code was this compile's own, which is what makes a link
     * failure in it this compiler's output failing: raised here, as {@link
     * GeneratedLinkage#rejectDefect} does, and not carried as something the applied code ended
     * with. Applied code that may be supplied from outside is carried by the constructor.
     */
    public static InvocationFailure ofGeneratedCode(Throwable cause) {
        GeneratedLinkage.rejectDefect(cause);
        return new InvocationFailure(cause);
    }
}
