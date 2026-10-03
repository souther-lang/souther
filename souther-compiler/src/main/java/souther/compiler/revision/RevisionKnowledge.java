package souther.compiler.revision;

import java.util.HashMap;
import java.util.Map;
import java.util.function.LongSupplier;

/**
 * What a revision has worked out: the answer every piece of {@link RevisionWork} came to under it.
 *
 * <p>One capability for all of it. What a revision knows is keyed by the work, so a new kind of
 * work is a new record and not a new place to keep answers or a new method to hand on — a reader
 * that holds this holds everything the revision knows, and one that rebuilds whatever it was handed
 * hands this on whole.
 *
 * <p>For a revision and no longer. What the work of a revision is about is settled by what the
 * sources say, and a revision that has moved is a world whose work may be other work; carried over,
 * the table would also hold every pattern and set an author wrote on the way to the one they meant.
 * So the table is dropped when the revision moves, which is asked when something is wanted rather
 * than announced by whatever moved.
 *
 * <p><b>Confined to the thread its store's walk is on.</b> Nothing here is synchronised: a store
 * answers its questions on the one thread holding it, and this is reached through the store.
 */
public interface RevisionKnowledge {

    /** What {@code work} comes to, as this revision already worked it out or works it out now. */
    <A> A settled(RevisionWork<A> work);

    /**
     * {@code work} done: the one place any of it is worked out, so whatever keeps the answers keeps
     * what this says.
     */
    static <A> A done(RevisionWork<A> work, RevisionKnowledge revision) {
        RevisionWorkDone.count(work.getClass());
        A answer = work.workedOut(revision);
        if (answer == null) {
            throw new IllegalStateException("work comes to an answer, empty or not: " + work);
        }
        return answer;
    }

    /**
     * How many times work of {@code kind} has been worked out rather than lent, for a test holding
     * a reader to how often it asks.
     *
     * <p>What a caller is held to is that work asked from many places is done for the first of them
     * — a shape, and not a speed.
     */
    static long timesDone(Class<?> kind) {
        return RevisionWorkDone.of(kind);
    }

    /**
     * Nothing kept, for a reading with no revision behind it.
     *
     * <p>A question asked outside a store has no revision to share with, so every asking does the
     * work again, and so does every piece of work it borrows.
     */
    RevisionKnowledge NONE = new RevisionKnowledge() {

        @Override
        public <A> A settled(RevisionWork<A> work) {
            return done(work, this);
        }
    };

    /**
     * Knowledge kept for as long as {@code revision} says the world it was worked out in is the
     * current one.
     */
    static RevisionKnowledge keptFor(LongSupplier revision) {
        return new Kept(revision);
    }

    /** The table, and the revision it was filled under. */
    final class Kept implements RevisionKnowledge {

        private final LongSupplier revision;

        private final Map<RevisionWork<?>, Object> answers = new HashMap<>();

        private long filledAt;

        private Kept(LongSupplier revision) {
            this.revision = revision;
            this.filledAt = revision.getAsLong();
        }

        // The cast holds because an entry is only ever put by doing its key, and a key of type
        // RevisionWork<A> comes to an A.
        @SuppressWarnings("unchecked")
        @Override
        public <A> A settled(RevisionWork<A> work) {
            Map<RevisionWork<?>, Object> current = current();
            Object known = current.get(work);
            if (known != null) {
                return (A) known;
            }
            // Done before it is put rather than inside the put: the work may borrow other work
            // from here while it is being done, which is the producer of what it borrows being
            // asked in the middle of this.
            A answer = done(work, this);
            current().put(work, answer);
            return answer;
        }

        /** What is known now: nothing, where the world has moved on since it was worked out. */
        private Map<RevisionWork<?>, Object> current() {
            long now = revision.getAsLong();
            if (now != filledAt) {
                answers.clear();
                filledAt = now;
            }
            return answers;
        }
    }
}
