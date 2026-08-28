package souther.compiler.query;

import souther.compiler.examples.Deadline;
import souther.compiler.execute.jvm.JvmDeadlines;
import souther.compiler.execute.jvm.JvmExampleDeadlines;

import java.time.Duration;

/**
 * Whichever arrangement this compilation was given, asked at the question.
 *
 * <p>One thing the implementation holds, so that a caller that says an arrangement after the
 * implementation was named is still the one that answers: an arrangement read once at construction
 * would be the one it replaced. That is all this is — the choice, and nothing about what a deadline
 * is or how one is kept, both of which are the machine's.
 *
 * <p>Nothing here reads the store. What the compilation was told is the wait, and the wait is a term:
 * it crosses the execution boundary and arrives as the argument. An arrangement that asked this
 * compilation for it instead would be the second reader that {@link JvmExampleDeadlines} exists to
 * do without.
 */
final class ChosenJvmExampleDeadlines implements JvmExampleDeadlines {

    /** What a build runs on until something says otherwise. */
    private JvmExampleDeadlines chosen = JvmDeadlines.onWorkers();

    /**
     * {@code arrangement} from here on, for a caller that runs this compilation's rows its own way.
     *
     * <p>Nothing is not an arrangement. A caller with none to say does not say one, and this taking
     * a null for it would leave a compilation that runs a row with nothing at all — which is not
     * what a caller passing the value it has not got means by it.
     */
    void chosen(JvmExampleDeadlines arrangement) {
        if (arrangement == null) {
            throw new IllegalArgumentException("a compilation's rows are run under an arrangement");
        }
        chosen = arrangement;
    }

    @Override
    public Deadline forThisCompile(Duration outerTimeout) {
        return chosen.forThisCompile(outerTimeout);
    }
}
