package souther.compiler.query;

/**
 * Who a store tells which question it is working out: each question as its answer starts being
 * computed, and again when that computation ends, whether it answered or threw.
 *
 * <p>A question answered from what the store kept is not told of: nothing was worked out. The two
 * calls for one question bracket every call for a question asked inside it, so the calls nest as
 * the questions do.
 *
 * <p>Told on the thread that holds the store. What a listener hands another thread is its own to
 * make safe.
 */
public interface Answering {

    /** Nobody is told. */
    Answering UNTOLD = new Answering() {
        @Override
        public void started(Key<?> key) {
        }

        @Override
        public void finished(Key<?> key) {
        }

        @Override
        public void startedOn(String module, String behavior) {
        }

        @Override
        public void finishedOn(String module, String behavior) {
        }
    };

    /** The answer of {@code key} starts being worked out. */
    void started(Key<?> key);

    /** The working out of {@code key} that started has ended. */
    void finished(Key<?> key);

    /**
     * The question in flight starts the part of its working out that is about {@code behavior}
     * of {@code module} ({@link Db#onOneBehavior}). Nested as a question asked there would be.
     */
    void startedOn(String module, String behavior);

    /** That part has ended. */
    void finishedOn(String module, String behavior);
}
