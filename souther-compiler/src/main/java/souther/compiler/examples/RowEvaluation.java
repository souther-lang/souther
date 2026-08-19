package souther.compiler.examples;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Messages;
import souther.compiler.diag.Note;
import souther.compiler.diag.TypeComparison;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.RowOutcome;

import java.util.List;
import java.util.Locale;

/**
 * What one row's run observed, and what the compiler said about it.
 *
 * <p>Two things and not one, because they answer to different readers. {@link #outcome} is what a
 * machine decides from — the disposition, where the row stopped, which case it expected and which it
 * saw — and it is the value an adequacy measure reads, which is what it was designed for. The
 * diagnostics are what a person is told: which value differed, at which position inside it, and in
 * the sentence the compiler already writes for that.
 *
 * <p>Answering with the outcome alone was the shape this had first, on the reasoning that no new
 * test-result model should be invented. That was the wrong saving. A row that failed a comparison
 * carries {@code FAILED}, {@code COMPARISON} and both arms, and where the two values differ inside
 * one arm that says nothing at all — a title read from the wrong column is the same outcome as a
 * title read from the right one. A consumer turning this into a test could say that a row failed and
 * not why, while the compiler had the sentence in hand and dropped it.
 *
 * <p>This is not a test-result model. Nothing here is about passing, failing, skipping or reporting;
 * it is one evaluation's two answers, kept apart the way this compiler keeps an observation and a
 * diagnostic apart everywhere else.
 *
 * @param outcome     what the run observed
 * @param diagnostics what was said about it, in the order it was said — empty where nothing was
 */
public record RowEvaluation(RowOutcome outcome, List<Diagnostic> diagnostics) {

    public RowEvaluation {
        if (outcome == null) {
            throw new IllegalArgumentException("an evaluation observed something");
        }
        diagnostics = List.copyOf(diagnostics);
    }

    /** Whether the row held: the behavior answered what the row says it owes. */
    public boolean held() {
        return outcome.disposition() == Disposition.HELD;
    }

    /**
     * What to say about this row, in one line per thing said.
     *
     * <p>For a consumer building an assertion message. Each line is the diagnostic's own text,
     * rendered the way a compile renders it, so a reader is told here what a compile would tell
     * them — a second wording of a mismatch would be a second answer to what the two values are.
     *
     * <p>The language is handed in and not picked here. What answers a reader has to say which
     * reader, and that is the consumer — a test framework's adapter, with its own option for it.
     * Picking one here would make a second surface out of something nobody looks at directly, and
     * the two would come apart.
     */
    public String shown(Locale locale) {
        StringBuilder said = new StringBuilder(outcome.target())
                .append(' ').append(outcome.identity().shown())
                .append(": ").append(outcome.disposition())
                .append('/').append(outcome.failurePhase());
        for (Diagnostic diagnostic : diagnostics) {
            said.append(System.lineSeparator()).append("  ")
                    .append(diagnostic.code()).append(": ")
                    .append(Messages.render(diagnostic.said(), locale));
            // The two values, where the diagnostic holds them. What a row's mismatch is about is
            // the pair rather than the sentence — the sentence says a row did not hold, and the
            // pair says which value it answered with.
            TypeComparison differs = diagnostic.diff();
            if (differs != null) {
                said.append(System.lineSeparator()).append("    expected: ")
                        .append(differs.expectedType())
                        .append(System.lineSeparator()).append("    answered: ")
                        .append(differs.actualType());
            }
            for (Note note : diagnostic.notes()) {
                said.append(System.lineSeparator()).append("    ")
                        .append(Messages.render(note.said(), locale));
            }
        }
        return said.toString();
    }
}
