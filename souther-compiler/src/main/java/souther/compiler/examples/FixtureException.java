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
     * The method a row's operand was emitted as is not in the classes this run was handed.
     *
     * <p>Not a rule about what a row may write: the operand was compiled, and what is missing is
     * this compiler's own output. It is said as the absence it is rather than as something the
     * author did.
     */
    static FixtureException nothingWasEmittedFor() {
        return new FixtureException("the value the row writes cannot be run:"
                + " no method was emitted for it, so there is nothing here to run");
    }
}
