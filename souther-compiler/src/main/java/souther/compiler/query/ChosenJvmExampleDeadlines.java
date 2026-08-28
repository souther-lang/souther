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
 *
 * <p><b>Said before anything runs a row, which is {@link Db#running}'s rule and not a second one.</b>
 * What runs a compilation's programs is beside the memos rather than in them, so no answer worked out
 * under one is invalidated by another being named, and the store would go on handing out the first
 * one's answers. That is why a store takes what runs its programs once. This is part of that thing:
 * a row run under one arrangement and an arrangement named afterwards is the same stale answer,
 * arrived at one level further in. So the choice closes the first time it is asked for, and a
 * replacement after that is refused rather than quietly not taken.
 */
final class ChosenJvmExampleDeadlines implements JvmExampleDeadlines {

    /** What a build runs on until something says otherwise. */
    private JvmExampleDeadlines chosen = JvmDeadlines.onWorkers();

    /** Whether a row has been run under {@link #chosen}. */
    private boolean answeredWith;

    /**
     * {@code arrangement} from here on, for a caller that runs this compilation's rows its own way.
     *
     * <p>Nothing is not an arrangement. A caller with none to say does not say one, and this taking
     * a null for it would leave a compilation that runs a row with nothing at all — which is not
     * what a caller passing the value it has not got means by it.
     *
     * @throws IllegalStateException where a row has already been run under the one this replaces
     */
    void chosen(JvmExampleDeadlines arrangement) {
        if (arrangement == null) {
            throw new IllegalArgumentException("a compilation's rows are run under an arrangement");
        }
        if (answeredWith) {
            throw new IllegalStateException("this compilation has already run rows under the"
                    + " arrangement it had, and answers worked out under one arrangement are not"
                    + " worked out again for another");
        }
        chosen = arrangement;
    }

    @Override
    public Deadline forThisCompile(Duration outerTimeout) {
        answeredWith = true;
        return chosen.forThisCompile(outerTimeout);
    }
}
