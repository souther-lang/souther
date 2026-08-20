package souther.compiler.observe;

/**
 * What applied the behavior for one row.
 *
 * <p>A reader that has to tell a row run against a {@code let} body from one run against an
 * implementation supplied from outside cannot get there from the disposition, which says
 * {@code HELD} for both, and deciding it at each reader is one question answered several times with
 * nothing holding the answers together.
 *
 * <p>This says what the run applied and nothing else. How a behavior is written is answered where it
 * is written ({@code Prepared.injected}), and a second answer to that question is what this
 * must not become. What the row cost is {@link Counting}, which covers the fixtures as well and so is
 * not a fact about the application alone.
 *
 * <p>A reader that has to tell the arms apart states that as a {@code switch} over this type rather
 * than as a test for one of them, so that the arm the reader did not consider is a compile error and
 * not a silent branch. What a reader must not do is branch on it for what it does not say:
 * {@code hits} answers what this compile's instrumentation saw, and a measure asking who applied the
 * behavior would answer two questions with one number.
 */
public sealed interface Applied {

    /**
     * The behavior was not applied.
     *
     * <p>A row whose fixtures did not build, one recorded against a behavior with nothing to run it,
     * one whose dependency had no fake — the reasons differ, and {@link Stage} and
     * {@link FailurePhase} are where they are said. What is said here is that no application
     * happened, so there is nothing that applied it.
     */
    record Nothing() implements Applied {}

    /** The classes this compile generated, applied through the loader this run built. */
    record GeneratedHere() implements Applied {}

    /**
     * An implementation this evaluation was given applied it.
     *
     * <p>Not {@code External}: where an implementation came from is a fact about a build, and what an
     * arm of this says is what applied the row.
     *
     * <p>It carries nothing. The question this answers is which of several things applied a row, not
     * which Java class it was, and a class in a test result is a runtime identity in a place that has
     * no use for one.
     */
    record Bound() implements Applied {}
}
