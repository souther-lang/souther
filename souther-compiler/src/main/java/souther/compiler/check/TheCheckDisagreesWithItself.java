package souther.compiler.check;

/**
 * The invariant-discharge check contradicting itself, which is the one thing it does not fail open
 * for.
 *
 * <p>Two failures arrive at {@link InvariantChecker#gaveUp} and they are not the same thing. A shape
 * the walk has no rule for is swallowed, and rightly: the run-time check stands, and a limit of this
 * analysis can never reject a valid program. This is the other one — one name given two values, one
 * clause given two answers, a region running between two sources, a value computed from itself.
 * Swallowed, it produces a behavior with no findings, which is exactly what a behavior whose
 * invariants all discharge produces, so the difference between "this could not be analysed" and
 * "every construction here is proven" stops being readable anywhere.
 *
 * <p>The type is what the boundary asks about, rather than a list of the ones it knows. A list is a
 * copy of this file kept somewhere else, and the way it goes wrong is silent: a check that gains a
 * new way to disagree with itself starts reporting that disagreement as an ordinary limit, and
 * nothing fails while it does. Extending this is what puts a new one on the right side of the
 * boundary.
 *
 * <p>What the boundary actually asks is
 * {@link souther.compiler.diag.TheCompilerDisagreesWithItself}, which this is the check's half of.
 * A region that is two places is refused where regions become places, which is a layer this class
 * cannot reach, and there is one question all the same.
 */
abstract class TheCheckDisagreesWithItself extends RuntimeException
        implements souther.compiler.diag.TheCompilerDisagreesWithItself {

    private static final long serialVersionUID = 1L;

    TheCheckDisagreesWithItself(String message) {
        super(message);
    }
}
