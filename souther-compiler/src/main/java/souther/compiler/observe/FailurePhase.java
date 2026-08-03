package souther.compiler.observe;

/**
 * Where an {@code example} row stopped, when it did.
 *
 * <p>{@link Stage} says what was established and this says what went wrong, which are not the same
 * cut: a row can reach {@link Stage#INVOKED} and stop there for a missing fake, for an
 * {@code unreachable} it reached, or for an invariant that aborted, and a report that has to tell
 * those apart cannot get there from the stage alone.
 */
public enum FailurePhase {

    /** Nothing went wrong. */
    NONE,

    /** An input fixture could not be built — a wrong arity, an unsupported form, a broken invariant. */
    INPUT_FIXTURE,

    /** The expectation could not be built, or names a case the behavior cannot produce. */
    EXPECTED_FIXTURE,

    /** A dependency had no fake, or a fake had no answer for the input it was given. */
    FAKE_RESOLUTION,

    /** Applying the behavior did not produce an answer. */
    INVOCATION,

    /** The behavior answered and the answer is not what the row expects. */
    COMPARISON,

    /** The evaluation did not finish within its budget. */
    TIMEOUT,

    /** Something the host was supposed to provide was not there. */
    INFRASTRUCTURE
}
