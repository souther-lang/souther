package souther.compiler.examples;

import souther.compiler.evaluate.DepthLimitExceeded;
import souther.compiler.evaluate.StepLimitExceeded;

/**
 * What a row makes of a failure the code it ran came back with.
 *
 * <p>The one reading of it. An evaluation that went over what it was allowed is about the budget and
 * belongs to whoever is holding the row to one, so it is raised on rather than read as a value that
 * would not build — read the other way the reason is lost and the report blames the wrong thing. A
 * stack that ran out is said as itself. Anything else is the value not being there, which is what
 * the row is told.
 *
 * <p>Apart from the invocation that produced the failure ({@link InvocationFailure}) because these
 * are two questions: what the generated program ended with, and what that means for the row. The
 * first is the same however the method was reached; the second is the row's, and {@code what} is how
 * the row names the thing it was running.
 */
final class RowFailures {

    private RowFailures() {
    }

    /** What {@code failure} means for a row that was running {@code what}. */
    static RuntimeException of(InvocationFailure failure, String what) {
        Throwable cause = failure.getCause();
        if (cause instanceof StepLimitExceeded || cause instanceof DepthLimitExceeded) {
            return (RuntimeException) cause;
        }
        if (cause instanceof StackOverflowError) {
            return new StackExhaustedException(what + " overflowed the stack");
        }
        return new FixtureException(what + " did not produce a value: "
                + (cause == null ? failure : cause.getMessage()));
    }
}
