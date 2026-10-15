package souther.compiler.evaluate;

/**
 * The evaluated code was asked to stop, because nobody is waiting for its answer any more.
 *
 * <p>Thrown by the generated code itself at a counted point, for the reason {@link
 * StepLimitExceeded} is: an interrupt is a request, and a pure computation reaches nothing that
 * would read it. Carries no stack trace and is a single instance, for the same reason too.
 */
public final class EvaluationAbandoned extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /** The one of these there is; see {@link DepthLimitExceeded#INSTANCE}. */
    @SuppressWarnings("StaticAssignmentOfThrowable")
    public static final EvaluationAbandoned INSTANCE = new EvaluationAbandoned();

    private EvaluationAbandoned() {
        super("the evaluation was abandoned", null, false, false);
    }
}
