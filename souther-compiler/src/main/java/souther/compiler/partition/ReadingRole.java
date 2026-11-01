package souther.compiler.partition;

/**
 * What a reading kept to be taken again does with one piece of the state of a {@link Pullback}.
 *
 * <p>A reading made at one place is taken again at another only where the second would come to the
 * same and leave the same behind. Every piece of state says here which of the two it is a part of,
 * or that it is neither, and a piece of state that says nothing is refused where the state is
 * first asked for ({@link ReadingState}).
 */
enum ReadingRole {

    /** The same at every reading of one Pullback. */
    FIXED,

    /**
     * What a reading may ask after, compared by what it holds. A reading is taken again only where
     * this holds the same.
     *
     * <p>What is held is compared with {@link Object#equals}, so the objects in it do not change
     * in place: a collection in one that is added to is a change nobody sees. A field held by
     * identity ({@link java.util.IdentityHashMap}) is refused here, since its values are compared
     * by identity and may change inside.
     */
    INPUT,

    /** What a reading may ask after, compared as the very object and never as an equal one: the
     *  lookups of the reader are made by identity, so a reading is the same only for the same
     *  object. */
    IDENTITY,

    /**
     * What a reading is made while nothing is in, and taken while nothing is in: the state of a
     * search whose body is being read, which the reading adds to what it reaches. A reading taken
     * would not add it, and a reading made would leave it half of what it is, so a search in
     * progress is no place to keep or to take one.
     */
    ABSENT,

    /** What a reading may ask after only whether there is one. */
    FLAG,

    /** What a reading may ask after, and is compared only for a reading that did: the aggregates
     *  of the way being read, each compared as the very aggregate. */
    ASKED,

    /** An input that a reading must also leave as it found it, because what it would have added
     *  is not there when the reading is taken again. */
    GUARDED,

    /** A place a reading adds to where there is one and never asks what is in: compared by
     *  whether there is one, and left as found. */
    WRITTEN,

    /** The rule being tried, which a reading must not have said anything into. */
    TRIAL,

    /** The parts met, in order, of which a candidate owns those from where it began. */
    LEDGER,

    /** The elements asked of, which a reading's footprint says. */
    FOOTPRINT,

    /** The readings left, which a reading is charged and a reading taken again is not. */
    BUDGET,

    /** Only added to, and never asked after by a reading: what a reading added is still there when
     *  it is taken again. */
    ACCRUES,

    /** Answers worked out once whatever asked, and so the same however they were first asked. */
    CACHE,

    /** The readings kept. */
    MEMO,

    /** A count that tells a reading what it did. */
    COUNTER
}
