package souther.compiler.observe;

/**
 * What applied the behavior for one row.
 *
 * <p>Today there is one answerer, so this is the same value for every row a compile ran. That is the
 * reason to record it rather than a reason not to: a reader that has to tell a row run against a
 * {@code let} body from one run against an implementation supplied from outside cannot get there from
 * the disposition, which says {@code HELD} for both, and deciding it at each reader is one question
 * answered several times with nothing holding the answers together.
 *
 * <p>This says what the run applied and nothing else. How a behavior is written is answered where it
 * is written ({@code ExampleVerifier.isPending}), and a second answer to that question is what this
 * must not become. What the row cost is {@link Counted}, which covers the fixtures as well and so is
 * not a fact about the application alone.
 *
 * <p>There is no arm for an implementation supplied from outside the compile. Nothing outside a
 * compile applies a behavior today, and an arm nothing writes is a statement about a run that does
 * not happen. When one arrives (#695), a reader that has to tell the arms apart states that as a
 * {@code switch} over this type rather than as a test for one of them, so that the arm the reader
 * did not consider is a compile error and not a silent branch.
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
}
