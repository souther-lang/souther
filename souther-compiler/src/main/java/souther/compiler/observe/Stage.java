package souther.compiler.observe;

/**
 * How far an {@code example} row got.
 *
 * <p>Separate from {@link Disposition} because how far a row reached and how it ended are different
 * questions with different readers. A row that never built its input tells a measure nothing about
 * the behavior; a row that ran and disagreed tells it which case the behavior actually produced. Both
 * are "failed", and collapsing them loses the second.
 */
public enum Stage {

    /** Nothing was established — the fixtures did not build. */
    NONE,

    /** The inputs and the expectation were built, so the row's values are known to be legal. */
    FIXTURES_VALIDATED,

    /** The behavior was applied. Whatever it answered, it answered. */
    INVOKED,

    /** The answer was compared against what the row expects. */
    COMPARED;

    public boolean reached(Stage at) {
        return compareTo(at) >= 0;
    }
}
