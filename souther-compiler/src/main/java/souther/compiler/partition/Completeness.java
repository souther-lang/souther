package souther.compiler.partition;

/**
 * Whether a search that came back with nothing had looked everywhere.
 *
 * <p>Two facts about the search and none about the model, added up as its readings answer: whether
 * there was a reading to search at all, and whether a bound stopped one of them with candidates it
 * had not tried. What may be said when nothing was found follows from those two, and follows here
 * rather than at each place a search gives up.
 *
 * <p>Read off a flag at the end of one loop, "every candidate was refused" and "this stopped
 * looking" came out as the same sentence. They are different news: the first sends a person to
 * change a rule, and the second sends them to widen a search over a row they can already write.
 *
 * <p><b>Not a reason a search failed.</b> Why the candidates that were tried did not answer is what
 * each of them came to; this is whether the ones that were not tried exist. A search that was
 * stopped is incomplete whatever the tried ones came to, which is why the bound outranks them.
 *
 * @param anyReading  whether what was asked for had a reading a row could be looked for at
 * @param anyCutShort whether a bound stopped one of those readings before its candidates ran out
 */
public record Completeness(boolean anyReading, boolean anyCutShort) {

    /** Before any reading has been searched. */
    public static final Completeness NOTHING_YET = new Completeness(false, false);

    /** With one more reading searched until its candidates ran out. */
    public Completeness searched() {
        return new Completeness(true, anyCutShort);
    }

    /** With one more reading a bound stopped. */
    public Completeness cutShort() {
        return new Completeness(true, true);
    }

    /**
     * What a search that found nothing may say it found nothing of.
     *
     * <p>The order between them is the whole of this. A bound that stopped one reading is a fact
     * about the search whatever the other readings came to, so it outranks their having been
     * searched to the end; and something with no reading at all was never searched, so it outranks
     * both.
     */
    public Nothing found() {
        if (!anyReading) {
            return Nothing.NO_READING;
        }
        return anyCutShort ? Nothing.SEARCH_STOPPED : Nothing.LOOKED_EVERYWHERE;
    }

    /** Which of the three ways a search comes back with nothing this was. */
    public enum Nothing {

        /** Nothing to look for: what was asked for has no reading a row could sit in. */
        NO_READING,

        /** A bound stopped the search with candidates it had not tried. */
        SEARCH_STOPPED,

        /** Every candidate of every reading was tried, and none of them answered. */
        LOOKED_EVERYWHERE
    }
}
