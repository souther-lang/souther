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

    /**
     * The values the row states do not keep what the behavior declares of what it answers.
     *
     * <p>Not {@link #EXPECTED_FIXTURE}, which is an expectation that could not be built. Here it was
     * built, and what it states and what the row was given are related in a way the model declares
     * cannot arise. Nor {@link #COMPARISON}, which is the answer disagreeing with the row: nothing
     * needs to have answered for this, and a row waiting for a body is held to it like any other.
     */
    ENSURES,

    /**
     * What was to apply the behavior could not be established as being of the module the row is
     * written for.
     *
     * <p>An implementation supplied from outside a compile reads a row's values by the declarations
     * it was built against, and those are of whatever build that was. Where they say something else
     * about what a value is — an invariant narrowed, a case added, a field renamed — a row handed over
     * is decided by the two builds disagreeing rather than by the model.
     *
     * <p>So the row is not handed over, and this is where it stopped. Not {@link #NONE}: the row was
     * to be run and something stopped it, and a row that said nothing went wrong while ending
     * undecided would be a state nothing produced. Not the model's failure either — {@link
     * Disposition#INCOMPLETE} is what it ends as, because what the row would have decided is exactly
     * what was not found out.
     */
    ANSWERER_ESTABLISHMENT,

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
