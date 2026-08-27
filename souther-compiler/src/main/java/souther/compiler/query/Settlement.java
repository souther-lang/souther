package souther.compiler.query;

/**
 * What one row a run offers would do about one thing the run is asked to offer a row for.
 *
 * <p>A conditional and never a measure. What this says is that <em>if</em> the row were written, the
 * item would be answered — which is a fact about the offering, not about the file. A row this run
 * composed is a question with no answer written yet, and nothing here makes it evidence that
 * anything is covered.
 *
 * <p><b>Three answers, because not found is not the same as not known.</b> A run nobody watched
 * cannot say which arms a row takes; a value the decoders would not build cannot be placed anywhere.
 * Read as a miss, either of them would let a row be dropped that was the only one answering
 * something — so only {@link Settles} may ever be acted on, and the other two differ in what a
 * reader may do about them: one is an answer, the other is the absence of one.
 */
public sealed interface Settlement {

    /** The row answers the item. */
    record Settles() implements Settlement {}

    /** It does not: this was read, and what it holds is not what the item asks for. */
    record DoesNotSettle() implements Settlement {}

    /** Nothing here can tell. */
    record Undetermined(Reason why) implements Settlement {

        public Undetermined {
            if (why == null) {
                throw new IllegalArgumentException("not knowing is for a reason");
            }
        }
    }

    /**
     * Why a row and an item could not be put together.
     *
     * <p>What was observed and never why the run was arranged as it was. Whether this build runs the
     * rows it composes is what the caller asked for, and a reason that named it would be answering a
     * question about the request in an answer about a row.
     */
    enum Reason {

        /** There is no account of the row's run, so which arms it takes is not something anything
         *  here saw. */
        NO_ACCOUNT_OF_THE_RUN,

        /** Nothing built the row's values, so where they sit is not something anything here read. */
        NOTHING_BUILT_THE_VALUES,

        /** Something built them and the model refused one, so there is no value to place. Beside
         *  the one above rather than folded into it: a run with nothing to build against found out
         *  nothing, and this found out that the value the row names is not one the model takes. */
        THE_VALUES_WERE_REFUSED,

        /** They were built and the walk to the item could not read one of them. */
        THE_VALUES_COULD_NOT_BE_READ
    }

    /** Whether a reader may act on this, which only one of the three allows. */
    default boolean settles() {
        return this instanceof Settles;
    }
}
