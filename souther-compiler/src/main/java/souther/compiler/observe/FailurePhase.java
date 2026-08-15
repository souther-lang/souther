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

    /** The evaluated code went through more counted points than the policy allows. What the row did
     * is what decided this, so it is decided the same way on every machine. */
    STEP_LIMIT,

    /** A recursive helper the row reaches went deeper than the policy allows. Also decided by what
     * the row did, and told apart from {@link #STEP_LIMIT} because what an author does about the two
     * is not the same. */
    DEPTH_LIMIT,

    /** The evaluation stopped answering and was given up on. Not a statement about the model: what
     * did not come back was not counted, so nothing here says the row would not have held. */
    TIMEOUT,

    /** The JVM stack ran out before the counted depth limit was reached. Also not a statement about
     * the model — how many frames a stack holds is decided by how large they are. */
    STACK_EXHAUSTED,

    /**
     * Something the host was supposed to provide was not there.
     *
     * <p>What produces it is a row that could not be handed to what was to apply it: the value the
     * row built could not be put in the form an answerer of other classes reads. Nothing about the
     * row was established, so it is recorded as undecided and not as a failure — the model may be
     * right, and nothing here saw enough to say.
     */
    INFRASTRUCTURE
}
