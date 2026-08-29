package souther.compiler.evaluate;

/**
 * The evaluated code went through more counted points than the policy allows.
 *
 * <p>Thrown by the generated code itself, which is what makes it a stop rather than a request: a
 * worker asked from outside to stop reaches no interrupt point in a pure computation, and goes on
 * running for as long as the JVM lives.
 *
 * <p>Carries no stack trace and is a single instance. It is thrown from a point the code passes
 * millions of times, and what it means is the same every time — where the row was when its budget ran
 * out says nothing an author can act on, because it is wherever the last step happened to be.
 */
public final class StepLimitExceeded extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public static final StepLimitExceeded INSTANCE = new StepLimitExceeded();

    private StepLimitExceeded() {
        super("the evaluation spent its step budget", null, false, false);
    }
}
