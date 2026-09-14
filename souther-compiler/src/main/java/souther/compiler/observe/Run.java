package souther.compiler.observe;

import souther.compiler.coverage.RunRecord;

import java.util.Objects;

/**
 * What became of one row's evaluation: what applied the behavior, and what this compile's own
 * counting read while the row ran.
 *
 * <p>A row's outcome used to record what the row turned out to be and not what produced the answer.
 * With one answerer — the bytecode this compile generated, applied through the loader the run builds
 * — that was invisible, and it stops being invisible the moment something else can answer.
 *
 * <p>The two here are different axes and are kept apart because a row's evaluation is not only its
 * application. A row builds its fixtures first, and a fixture applies whatever helpers it names, so
 * counted points are spent before the behavior is reached and are spent by rows that never reach it:
 * a fixture that costs eleven points and then breaks an invariant is a row that applied nothing and
 * did eleven points of counted work. Reading the count off the application would have thrown that
 * away, and reading the application off the count would say a row that spent nothing applied nothing.
 *
 * @param applied  what applied the behavior, if anything did
 * @param counting what this compile counted of the row's evaluation — application and fixtures
 *                 alike — or that it was never read
 */
public record Run(Applied applied, Counting counting) {

    public Run {
        Objects.requireNonNull(applied, "a row says what applied the behavior, or that nothing did");
        Objects.requireNonNull(counting, "a row says what this compile counted of it, or that it did not");
    }

    /** A row that applied nothing and was read to have spent nothing. */
    public static Run nothing() {
        return new Run(new Applied.Nothing(),
                new Counting.Read(0L, new RunRecord.NoAccount()));
    }
}
