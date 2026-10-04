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
        RevisionWorkDone.entering(revision, work);
        try {
            // Counted once it is known to be done, and not where it was refused as one already
            // under way: a piece of work asked for while it is being done was not worked out.
            RevisionWorkDone.count(work.getClass());
            A answer = work.workedOut(revision);
            if (answer == null) {
                throw new IllegalStateException("work comes to an answer, empty or not: " + work);
            }
            return answer;
        } finally {
            RevisionWorkDone.leaving(revision, work);
        }
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
     * current one, with what doing each piece of work read of {@code store}.
     *
     * <p>The store is not optional. A piece of work is done for the question that asked first and
     * lent to every question after it, and a question of the store is kept by what it read: lent
     * the answer alone, a later question read nothing to have it, and is kept over an edit to what
     * the work read. So what the work read is kept beside its answer and read again for whoever is
     * lent it. Knowledge with nothing to watch says so with {@link StoreWork#UNWATCHED}.
     */
    static RevisionKnowledge keptFor(LongSupplier revision, StoreWork store) {
        return new Kept(revision, store);
    }

    /** The table, the revision it was filled under, and the store the work in it read. */
    final class Kept implements RevisionKnowledge {

        private final LongSupplier revision;

        private final StoreWork store;

        private final Map<RevisionWork<?>, StoreWork.Made<?>> answers = new HashMap<>();

        private long filledAt;

        private Kept(LongSupplier revision, StoreWork store) {
            this.revision = revision;
            this.store = store;
            this.filledAt = revision.getAsLong();
        }

        // The cast holds because an entry is only ever put by doing its key, and a key of type
        // RevisionWork<A> comes to an A.
        @SuppressWarnings("unchecked")
        @Override
        public <A> A settled(RevisionWork<A> work) {
            Map<RevisionWork<?>, StoreWork.Made<?>> current = current();
            StoreWork.Made<?> known = current.get(work);
            if (known != null) {
                // What doing it read is what whoever is lent it read: they are handed the answer
                // rather than working it out, and an edit to what it was worked out from has to
                // reach them.
                known.reads().here();
                return (A) known.value();
            }
            // Done before it is put rather than inside the put: the work may borrow other work
            // from here while it is being done, which is the producer of what it borrows being
            // asked in the middle of this. Watched, so that what it read is read by the question
            // doing it and kept for the ones it is lent to.
            StoreWork.Made<A> made = store.watching(() -> done(work, this));
            current().put(work, made);
            return made.value();
        }

        /** What is known now: nothing, where the world has moved on since it was worked out. */
        private Map<RevisionWork<?>, StoreWork.Made<?>> current() {
            long now = revision.getAsLong();
            if (now != filledAt) {
                answers.clear();
                filledAt = now;
            }
            return answers;
        }
    }
}
