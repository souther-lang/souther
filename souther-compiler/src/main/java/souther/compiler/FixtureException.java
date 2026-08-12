package souther.compiler;

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
     * A call a fixture cannot run. Two different things reach here and a row is told which: a
     * standard-library function, which a fixture may not apply however it is implemented, and a
     * helper of this module that no method was emitted for.
     *
     * <p>Written once because three readings refuse the same call — the two that build a fixture and
     * the one that applies a helper — and three copies of a sentence are three sentences that can
     * come to say different things about one rule.
     *
     * @param written  the call as the row spelled it, which is what a report underlines
     * @param reached  the name the callee was looked up by, which is what decides the reason
     */
    static FixtureException cannotBeCalled(String written, String reached) {
        return new FixtureException("`" + written + "` cannot be called from an example fixture: "
                + (Prelude.isLibraryFunction(reached)
                        ? "a standard-library function is not one a fixture may apply. Compute the"
                                + " value in a `let` helper and apply that instead"
                        : "no method was emitted for it, so there is nothing here to run"));
    }
}
