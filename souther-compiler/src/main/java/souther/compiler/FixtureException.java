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
}
