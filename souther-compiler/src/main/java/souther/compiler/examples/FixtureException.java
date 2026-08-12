package souther.compiler.examples;

/**
 * A fixture an {@code example} writes cannot be built: an unsupported form, a value that breaks the
 * type's invariant, a function with no method to apply, or a value a helper returned that cannot be
 * read back. Reported as the row's own fixture error (E1903, E1908) rather than as a failed example —
 * the row states nothing until its fixtures are built.
 */
final class FixtureException extends RuntimeException {
    FixtureException(String message) {
        super(message);
    }

    /**
     * A call a fixture cannot run, because nothing emitted a method for what it names.
     *
     * <p>Says that and nothing more. It used to tell a standard-library function apart and refuse it
     * as one — that a fixture may not apply a library function however it is implemented — and that
     * was never a rule this compiler held: a library function written in Souther is emitted for the
     * row that applies it and runs (#680). What is left here is the absence itself, which is a fact
     * about this build and not a rule about the library.
     *
     * <p>Written once because two readings refuse the same call — the one that builds a fixture and
     * the one that applies a helper — and two copies of a sentence are two sentences that can come to
     * say different things about one rule.
     *
     * @param written the call as the row spelled it, which is what a report underlines
     */
    static FixtureException cannotBeCalled(String written) {
        return new FixtureException("`" + written + "` cannot be called from an example fixture:"
                + " no method was emitted for it, so there is nothing here to run");
    }
}
